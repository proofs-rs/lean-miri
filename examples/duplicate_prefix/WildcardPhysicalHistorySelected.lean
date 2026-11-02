import duplicate_prefix.GlobalAddressPhysicalLocalRows
import duplicate_prefix.WildcardPhysicalRowHistoryConsumers
namespace DuplicatePrefix.WildcardPhysicalHistorySelected
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- Selected source facts consumed by exposed-hit append/pool fullcall inputs.
Tree allocator/permission/runtime contracts are separate: address history
alone cannot constrain an arbitrary initial allocation's borrow tree. -/
structure Hit {K} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64) where
  id : AllocId
  base : UInt64
  entry : LocalAllocation Provenance BorrowTree K
  exposed : addresses.exposed.contains id=true
  geometry : WildcardGeneralHitReborrow.Geometry addresses.intToPtrMap address base id entry.allocation.byteSize
  cached : addresses.baseAddr.find? (fun row=>row.allocId==id)=some ⟨id,base⟩
  present : memory.live.find? (fun row=>row.1==id)=some (id,entry)

def Unresolved {K} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64) : Prop :=
  WildcardOrderedMissAddress.Miss addresses address ∨ WildcardGapResolver.Miss addresses memory address

/-- Exhaustive source selection now forms both actual local backing and cache
for the hit branch. No manual branch, selected lookup, final cache coherence,
or post-operation success appears among its inputs. -/
theorem classify {K} [DecidableEq K] (sizes : AllocId→Size)
    {memory : MemoryState Provenance BorrowTree K} {addresses : GlobalAddressState}
    (history : GlobalAddressPhysicalRowHistory.History sizes memory addresses) (address : UInt64) :
    Unresolved memory addresses address ∨ Nonempty (Hit memory addresses address) := by
  rcases WildcardPhysicalRowHistoryConsumers.classify sizes history address with miss | ⟨id,base,exposed,geometry⟩ | gap
  · exact Or.inl (Or.inl miss)
  · obtain ⟨entry,present,sizeEq,cached⟩:=GlobalAddressPhysicalLocalRows.hit sizes history address base id geometry
    rw [sizeEq] at geometry
    exact Or.inr ⟨⟨id,base,entry,exposed,geometry,cached,present⟩⟩
  · exact Or.inl (Or.inr gap)

/-- Actual typed zero-byte wildcard resolution is total and state preserving
for every physical-row history under nonstrict provenance and the real
64-bit arithmetic provider. Hit location/relative offset come from the source
selected local allocation, not an external resolver-success premise. -/
theorem resolve {K U} [DecidableEq K] (sizes : AllocId→Size)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U)
    (history : GlobalAddressPhysicalRowHistory.History sizes before.machine.memory before.machine.user.addresses)
    (address : UInt64) (mode : before.machine.user.addresses.provenanceMode≠.strict)
    (width : pointers.arithmetic=⟨Size.ofBytes 8⟩) :
    (Unresolved before.machine.memory before.machine.user.addresses address ∧
      TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before=.ok none before) ∨
    ∃hit : Hit before.machine.memory before.machine.user.addresses address,
      TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before=
        .ok (some ⟨hit.id,Size.ofBytes (address-hit.base),.wildcard⟩) before := by
  rcases classify sizes history address with unresolved | selected
  · apply Or.inl
    refine ⟨unresolved,?_⟩
    rcases unresolved with miss | gap
    · exact WildcardOrderedMissAddress.resolve_miss pointers before address mode miss
    · exact WildcardGapResolver.resolve_miss pointers before address mode gap
  · obtain ⟨hit⟩ := selected
    exact Or.inr ⟨hit,WildcardGeneralHitReborrow.resolve pointers before address hit.base hit.id hit.entry
      hit.geometry width mode hit.exposed hit.cached hit.present⟩
end DuplicatePrefix.WildcardPhysicalHistorySelected
