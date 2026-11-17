import duplicate_prefix.WildcardMissAddress
import duplicate_prefix.WildcardOrderedHitAddress

namespace DuplicatePrefix.WildcardOrderedMissAddress
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Raw address geometry for unresolved wildcard provenance: below every row,
or an exact unexposed row in an arbitrary finite strictly ordered inverse map.
The exact-hit branch consults neither size nor liveness metadata. -/
def Miss (state : GlobalAddressState) (address : UInt64) : Prop :=
  (∀ entry ∈ state.intToPtrMap, address < entry.address) ∨
  ∃ id position, position < state.intToPtrMap.size ∧
    WildcardInteriorHitAddress.Ordered state.intToPtrMap ∧
    state.intToPtrMap[position]? = some ⟨address,id⟩ ∧ state.exposed.contains id = false

/-- The unchanged source binary search genuinely finds the raw ordered row;
source exposure rejection then returns unresolved without metadata callbacks. -/
theorem allocation_miss (state : GlobalAddressState) (address : UInt64) (hooks : AddressLookupHooks)
    (mode : state.provenanceMode ≠ .strict) (miss : Miss state address) :
    state.allocIdFromAddr address 0 hooks = .ok none := by
  rcases miss with below | ⟨id,position,valid,ordered,row,unexposed⟩
  · exact WildcardMissAddress.allocation_miss state address hooks mode (Or.inl below)
  · have search := WildcardOrderedHitAddress.inverse_hit state.intToPtrMap address id position valid ordered row
    have missing : id ∉ state.exposed := by simpa using unexposed
    unfold GlobalAddressState.allocIdFromAddr
    unfold_global_data ".GlobalAddressState.inverseSearch"
    simp [mode,search,row,missing,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

theorem pointer_miss (state : GlobalAddressState) (address : UInt64) (hooks : AddressLookupHooks)
    (arithmetic : PointerArithmetic) (mode : state.provenanceMode ≠ .strict)
    (miss : Miss state address) :
    state.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0 hooks arithmetic = .ok none := by
  simp only [GlobalAddressState.ptrGetAlloc,Pointer.new,Size.ofBytes,allocation_miss state address hooks mode miss,
    bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

/-- The real typed-retag resolver preserves an unresolved wildcard pointer's
state. Its zero-sized check does not skip this resolution operation. -/
theorem resolve_miss {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address : UInt64)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (miss : Miss before.machine.user.addresses address) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before =
      .ok none before := by
  have resolution := pointer_miss before.machine.user.addresses address
    (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),
      fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
    pointers.arithmetic mode miss
  simp only [Pointer.new] at resolution
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,resolution,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]

end DuplicatePrefix.WildcardOrderedMissAddress
