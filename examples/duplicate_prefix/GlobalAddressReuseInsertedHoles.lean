import duplicate_prefix.GlobalAddressReuseTakePairwise
namespace DuplicatePrefix.GlobalAddressReuseInsertedHoles
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressReuseContents GlobalAddressReuseHoleGeometry GlobalAddressReusePairwise GlobalAddressReuseRemaining
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

theorem present (pool : ReusePool) (bucket : Array ReusableAddress) (member : bucket∈pool.pool)
    (entry : ReusableAddress) (stored : entry∈bucket) : ∃ slot,peek pool.pool slot=some entry := by
  obtain ⟨bi,bv,be⟩:=Array.mem_iff_getElem.mp member
  obtain ⟨ei,ev,ee⟩:=Array.mem_iff_getElem.mp stored
  refine ⟨(bi,ei),?_⟩
  simp only [peek,Array.getElem?_eq_getElem bv,Option.bind_some,be,Array.getElem?_eq_getElem ev,ee]

theorem inserted (pool : ReusePool) (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (initial : Contents pool (Hole entries sizes)) (entry : ReusableAddress) (remaining : Remaining pool entry)
    (id : AllocId) (size : Size) (sizeEq : sizes id=size) (fits : size.bytes≤entry.size.bytes)
    (cut : Nat) (bounded : cut≤entries.size) :
    Contents pool (Hole (entries.insertIdx cut ⟨entry.address,id⟩ bounded) sizes) := by
  intro bucket member other stored
  have old:=initial bucket member other stored
  obtain ⟨slot,present⟩:=present pool bucket member other stored
  have separate:=remaining slot other present
  have fitsNat:=UInt64.le_iff_toNat_le.mp fits
  refine ⟨old.1,?_⟩
  intro row rowPresent
  rcases Array.mem_insertIdx.mp rowPresent with same | previous
  · subst row
    simp only [sizeEq]
    rcases separate with left | right
    · exact Or.inl (by omega)
    · exact Or.inr right
  · exact old.2 row previous

/-- The actual take forms reusable holes against the inverse map AFTER its
returned range becomes live. Pairwise stored-hole geometry supplies the new
row separation, including zero-size footprints. No remaining-hole premise
about the returned post-state is assumed. -/
theorem take (pool : ReusePool) (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (initial : Contents pool (Hole entries sizes)) (pairwise : Pairwise pool)
    (reuse cross : Bool) (selection : Nat) (size : Size) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId)
    (id : AllocId) (sizeEq : sizes id=size) :
    let result:=pool.takeAddr reuse cross selection size align kind thread
    Pairwise result.state ∧ ∀ used,result.outcome=.ok (some used) →
      ∀ cut (bounded : cut≤entries.size),
      Contents result.state (Hole (entries.insertIdx cut ⟨used.address,id⟩ bounded) sizes) := by
  dsimp only
  have facts:=GlobalAddressReuseTakePairwise.take pool (Hole entries sizes) initial pairwise reuse cross selection size align kind thread
  refine ⟨facts.1,?_⟩
  intro used actual cut bounded
  obtain ⟨entry,_,same,fits,remaining⟩:=facts.2.2 used actual
  rw [same]
  exact inserted _ entries sizes facts.2.1 entry remaining id size sizeEq fits cut bounded
/-- Source cache insertion preserves all remaining reuse holes after the
selected hole becomes a live inverse row. The operation itself computes and
checks the cut; no cache success is assumed. -/
theorem cache (addresses : GlobalAddressState) (pool : ReusePool) (sizes : AllocId → Size)
    (initial : Contents pool (Hole addresses.intToPtrMap sizes))
    (entry : ReusableAddress) (remaining : Remaining pool entry)
    (id : AllocId) (size : Size) (sizeEq : sizes id=size) (fits : size.bytes≤entry.size.bytes)
    (uncached : addresses.baseAddr.find? (fun row=>row.allocId==id)=none)
    (nonzero : entry.address≠0) (cut : Nat)
    (partition : WildcardInteriorHitAddress.Cut addresses.intToPtrMap entry.address cut) :
    Contents pool (Hole (addresses.cacheAddress id entry.address).state.intToPtrMap sizes) := by
  have search:=WildcardInteriorHitAddress.inverse_cut addresses.intToPtrMap entry.address cut partition
  have nz : (entry.address==0)=false := by simpa using nonzero
  unfold GlobalAddressState.cacheAddress
  unfold_internal ".GlobalAddressState.findBase"
  simp only [uncached,Option.map_none,search,nz,Bool.false_eq_true,↓reduceIte,partition.1,↓reduceDIte]
  exact inserted pool addresses.intToPtrMap sizes initial entry remaining id size sizeEq fits cut partition.1

end DuplicatePrefix.GlobalAddressReuseInsertedHoles
