import duplicate_prefix.GlobalAddressReuseHoleGeometry
import duplicate_prefix.GlobalAddressReuseAddContents
namespace DuplicatePrefix.GlobalAddressReuseFreeHoles
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressReuseContents GlobalAddressReuseHoleGeometry GlobalAddressRangeFormation WildcardEmptyFamilyFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

theorem strong (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (ordered : WildcardInteriorHitAddress.Ordered entries) (apart : Apart entries sizes)
    (left right : Nat) (valid : right<entries.size) (less : left<right) :
    entries[left].address.toNat+max 1 (sizes entries[left].allocId).bytes.toNat ≤ entries[right].address.toNat := by
  have first:=apart left right valid less
  have second:=UInt64.lt_iff_toNat_lt.mp (ordered left right less valid)
  omega

/-- Freeing a stored source range creates a separated hole even for size zero:
strict inverse ordering supplies the one-byte uniqueness footprint. -/
theorem erased_hole (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (ordered : WildcardInteriorHitAddress.Ordered entries) (apart : Apart entries sizes)
    (id : AllocId) (address : UInt64) (nonzero : address≠0) (size : Size) (sizeEq : sizes id=size)
    (position : Nat) (valid : position<entries.size) (row : entries[position]?=some ⟨address,id⟩)
    (thread : AddressThreadId) (clock : VClock) : Hole (entries.eraseIdx position valid) sizes ⟨address,size,thread,clock⟩ := by
  have actual : entries[position]=⟨address,id⟩:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans row)
  refine ⟨nonzero,?_⟩
  intro current member
  obtain ⟨index,indexValid,different,equal⟩:=Array.mem_eraseIdx_iff_getElem.mp member
  by_cases before : index<position
  · apply Or.inl
    have separated:=strong entries sizes ordered apart index position valid before
    simpa only [actual,equal] using separated
  · apply Or.inr
    have after : position<index:=by omega
    have separated:=strong entries sizes ordered apart position index indexValid after
    simpa only [actual,equal,sizeEq] using separated

theorem restrict (pool : ReusePool) (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (initial : Contents pool (Hole entries sizes)) (position : Nat) (valid : position<entries.size) :
    Contents pool (Hole (entries.eraseIdx position valid) sizes) := by
  intro bucket member entry stored
  have old:=initial bucket member entry stored
  refine ⟨old.1,?_⟩
  intro current present
  exact old.2 current (Array.mem_of_mem_eraseIdx present)

/-- Real source free plus its actual addAddr reuse operation forms separated
stored holes against the post-free inverse vector, including pool-error
prefixes. The base cache is retained; its old row is never treated as live. -/
theorem free (addresses : GlobalAddressState) (generation : AddressGenerationState) (sizes : AllocId → Size)
    (generationEq : addresses.generation=some generation)
    (ordered : WildcardInteriorHitAddress.Ordered addresses.intToPtrMap) (apart : Apart addresses.intToPtrMap sizes)
    (initial : Contents generation.reusePool (Hole addresses.intToPtrMap sizes))
    (id : AllocId) (address : UInt64) (nonzero : address≠0) (size : Size) (sizeEq : sizes id=size)
    (position : Nat) (valid : position<addresses.intToPtrMap.size)
    (row : addresses.intToPtrMap[position]?=some ⟨address,id⟩)
    (cached : addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,address⟩)
    (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId) (choice : Bool) (clock : Unit → VClock) :
    let result:=addresses.freeAllocId id size align kind thread choice clock
    ∃ nextGeneration, result.state.generation=some nextGeneration ∧
      Contents nextGeneration.reusePool (Hole result.state.intToPtrMap sizes) := by
  dsimp only
  have frame:=GlobalAddressFreeHistoryFormation.free_erases addresses id address position valid ordered row cached size align kind thread choice clock
  have hole:=erased_hole addresses.intToPtrMap sizes ordered apart id address nonzero size sizeEq position valid row thread (clock ())
  have kept:=restrict generation.reusePool addresses.intToPtrMap sizes initial position valid
  have added:=GlobalAddressReuseAddContents.add generation.reusePool (Hole (addresses.intToPtrMap.eraseIdx position valid) sizes)
    kept choice address size align kind thread clock hole
  rw [frame.1]
  have search:=WildcardOrderedHitAddress.inverse_hit addresses.intToPtrMap address id position valid ordered row
  have actual : addresses.intToPtrMap[position]=⟨address,id⟩:=Option.some.inj ((Array.getElem?_eq_getElem valid).symm.trans row)
  unfold GlobalAddressState.freeAllocId
  unfold_internal ".GlobalAddressState.findBase"
  simp only [cached,Option.map_some,search,Bool.not_true,Bool.false_eq_true,↓reduceIte,valid,↓reduceDIte,actual,bne_self_eq_false,generationEq]
  cases outcome : (generation.reusePool.addAddr choice address size align kind thread clock).outcome <;>
    simp only [outcome] <;>
    exact ⟨{generation with reusePool:=(generation.reusePool.addAddr choice address size align kind thread clock).state},rfl,added⟩
end DuplicatePrefix.GlobalAddressReuseFreeHoles
