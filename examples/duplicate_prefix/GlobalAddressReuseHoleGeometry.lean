import duplicate_prefix.GlobalAddressReuseTakeContents
namespace DuplicatePrefix.GlobalAddressReuseHoleGeometry
open Miri Miri.Concurrency Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open GlobalAddressReuseContents GlobalAddressReuseTakeContents GlobalAddressRangeFormation
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

def Separated (entries : Array InverseAddressEntry) (sizes : AllocId → Size) (address : UInt64) (size : Size) : Prop :=
  ∀ row ∈ entries,
    row.address.toNat + max 1 (sizes row.allocId).bytes.toNat ≤ address.toNat ∨
    address.toNat + max 1 size.bytes.toNat ≤ row.address.toNat

def Hole (entries : Array InverseAddressEntry) (sizes : AllocId → Size) (entry : ReusableAddress) : Prop :=
  entry.address ≠ 0 ∧ Separated entries sizes entry.address entry.size

theorem shrink (entries : Array InverseAddressEntry) (sizes : AllocId → Size) (address : UInt64)
    (before after : Size) (fits : after.bytes ≤ before.bytes) (initial : Separated entries sizes address before) :
    Separated entries sizes address after := by
  intro row member
  rcases initial row member with left | right
  · exact Or.inl left
  · apply Or.inr
    have le := UInt64.le_iff_toNat_le.mp fits
    omega

/-- A disjoint stored hole has no exact live inverse address. The actual
ordered search supplies its insertion cut; its left/right numeric placement
is derived from hole separation, not supplied as a cache-success premise. -/
theorem placement (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (ordered : WildcardInteriorHitAddress.Ordered entries) (id : AllocId) (size : Size) (sizeEq : sizes id=size)
    (address : UInt64) (initial : Separated entries sizes address size) :
    ∃ cut, WildcardInteriorHitAddress.Cut entries address cut ∧ Placement entries sizes id address cut := by
  have different : ∀ row∈entries,row.address≠address := by
    intro row member equal
    rcases initial row member with left | right
    all_goals rw [equal] at *;omega
  obtain ⟨cut,actual,partition⟩ := WildcardEmptyAddressClassification.inverse_cut entries address ordered different
  refine ⟨cut,partition,?_,?_⟩
  · intro index valid before
    have bound:=partition.2.1 index valid before
    have below:=UInt64.lt_iff_toNat_lt.mp bound
    rcases initial entries[index] (Array.getElem_mem valid) with left | right
    · omega
    · omega
  · intro index valid after
    have bound:=partition.2.2 index valid after
    have above:=UInt64.lt_iff_toNat_lt.mp bound
    rw [sizeEq]
    rcases initial entries[index] (Array.getElem_mem valid) with left | right
    · omega
    · omega

/-- Every actual take outcome is handled. A returned address is a nonzero
source-stored hole, whose size bound and physical separation form a valid
cache insertion partition for the new allocation. Error/none branches make
no successful-allocation assertion. -/
theorem take_separated (pool : ReusePool) (entries : Array InverseAddressEntry) (sizes : AllocId → Size)
    (initial : Contents pool (Hole entries sizes)) (ordered : WildcardInteriorHitAddress.Ordered entries)
    (id : AllocId) (size : Size) (sizeEq : sizes id=size)
    (reuse cross : Bool) (selection : Nat) (align : Align) (kind : AddressMemoryKind) (thread : AddressThreadId) :
    let result := pool.takeAddr reuse cross selection size align kind thread
    Contents result.state (Hole entries sizes) ∧
    ∀ used, result.outcome=.ok (some used) → used.address≠0 ∧
      ∃ cut, WildcardInteriorHitAddress.Cut entries used.address cut ∧ Placement entries sizes id used.address cut := by
  dsimp only
  have result:=take pool (Hole entries sizes) initial reuse cross selection size align kind thread
  refine ⟨result.1,?_⟩
  intro used actual
  obtain ⟨entry,hole,same,fits⟩:=result.2 used actual
  have separated:=shrink entries sizes entry.address entry.size size fits hole.2
  rw [same]
  exact ⟨hole.1,placement entries sizes ordered id size sizeEq entry.address separated⟩
end DuplicatePrefix.GlobalAddressReuseHoleGeometry
