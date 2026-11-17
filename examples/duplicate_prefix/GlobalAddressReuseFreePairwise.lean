import duplicate_prefix.GlobalAddressReuseAddPairwise
namespace DuplicatePrefix.GlobalAddressReuseFreePairwise
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressReuseContents GlobalAddressReuseHoleGeometry GlobalAddressReusePairwise
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

theorem released (pool : ReusePool) (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (initial : Contents pool (Hole entries sizes))
    (id : AllocId) (address : UInt64) (size : Size) (sizeEq : sizes id=size)
    (position : Nat) (valid : position<entries.size) (row : entries[position]?=some ⟨address,id⟩)
    (thread : AddressThreadId) (clock : VClock) : Contents pool (Separate ⟨address,size,thread,clock⟩) := by
  have actual : entries[position]=⟨address,id⟩:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans row)
  intro bucket member entry stored
  have separated:=(initial bucket member entry stored).2 entries[position] (Array.getElem_mem valid)
  simpa only [actual,sizeEq,Separate] using separated

theorem free (addresses : GlobalAddressState) (generation : AddressGenerationState) (sizes : AllocId → Size)
    (generationEq : addresses.generation=some generation)
    (ordered : WildcardInteriorHitAddress.Ordered addresses.intToPtrMap)
    (initial : Contents generation.reusePool (Hole addresses.intToPtrMap sizes))
    (pairwise : Pairwise generation.reusePool)
    (id : AllocId) (address : UInt64) (nonzero : address≠0) (size : Size) (sizeEq : sizes id=size)
    (position : Nat) (valid : position<addresses.intToPtrMap.size)
    (row : addresses.intToPtrMap[position]?=some ⟨address,id⟩)
    (cached : addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,address⟩)
    (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId) (choice : Bool) (clock : Unit → VClock) :
    let result:=addresses.freeAllocId id size align kind thread choice clock
    ∃ nextGeneration, result.state.generation=some nextGeneration ∧
      Pairwise nextGeneration.reusePool := by
  dsimp only
  have frame:=GlobalAddressFreeHistoryFormation.free_erases addresses id address position valid ordered row cached size align kind thread choice clock
  have separate:=released generation.reusePool addresses.intToPtrMap sizes initial id address size sizeEq position valid row thread (clock ())
  have added:=GlobalAddressReuseAddPairwise.add generation.reusePool pairwise choice address size align kind thread clock separate
  have search:=WildcardOrderedHitAddress.inverse_hit addresses.intToPtrMap address id position valid ordered row
  have actual : addresses.intToPtrMap[position]=⟨address,id⟩:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans row)
  unfold GlobalAddressState.freeAllocId
  unfold_internal ".GlobalAddressState.findBase"
  simp only [cached,Option.map_some,search,Bool.not_true,Bool.false_eq_true,↓reduceIte,valid,↓reduceDIte,actual,bne_self_eq_false,generationEq]
  cases outcome : (generation.reusePool.addAddr choice address size align kind thread clock).outcome <;>
    simp only [outcome] <;>
    exact ⟨{generation with reusePool:=(generation.reusePool.addAddr choice address size align kind thread clock).state},rfl,added⟩
end DuplicatePrefix.GlobalAddressReuseFreePairwise
