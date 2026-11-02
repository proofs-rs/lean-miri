import duplicate_prefix.WildcardInteriorHitAddress
import duplicate_prefix.WildcardMetadataGap
namespace DuplicatePrefix.WildcardUnexposedInteriorAddress
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Raw insertion-cut geometry with a size-backed unexposed predecessor.
The source queries size before rejecting exposure; no liveness is required. -/
def Geometry (state : GlobalAddressState) (address : UInt64) (sizeOf : AllocId → Option Size) : Prop :=
  ∃ position row size,WildcardInteriorHitAddress.Cut state.intToPtrMap address (position+1) ∧
    state.intToPtrMap[position]? = some row ∧ sizeOf row.allocId = some size ∧ state.exposed.contains row.allocId = false

theorem allocation (state : GlobalAddressState) (address : UInt64) (hooks : AddressLookupHooks)
    (mode : state.provenanceMode ≠ .strict) (geometry : Geometry state address hooks.sizeOf) :
    state.allocIdFromAddr address 0 hooks = .ok none := by
  obtain ⟨position,row,size,partition,present,known,unexposed⟩ := geometry
  have search := WildcardInteriorHitAddress.inverse_cut state.intToPtrMap address (position+1) partition
  have missing : row.allocId ∉ state.exposed := by simpa using unexposed
  unfold GlobalAddressState.allocIdFromAddr
  unfold_global_data ".GlobalAddressState.inverseSearch"
  by_cases inside : address-row.address < size.bytes
  all_goals simp [mode,search,present,known,inside,missing,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]

theorem resolve {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (before : ValidityMachine.State K U) (address : UInt64)
    (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
    (geometry : Geometry before.machine.user.addresses address (fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size))) :
    TypedValidityProviders.resolveAllocation pointers (Pointer.new (some .wildcard) (Size.ofBytes address)) before = .ok none before := by
  have resolved := allocation before.machine.user.addresses address
    (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
    mode geometry
  have pointer : before.machine.user.addresses.ptrGetAlloc (Pointer.new .wildcard (Size.ofBytes address)) 0
      (⟨fun id => (before.machine.memory.getAllocInfo id).toOption.map (·.size),fun id => some (before.machine.memory.isAllocLive id)⟩ : AddressLookupHooks)
      pointers.arithmetic = .ok none := by
    simp only [GlobalAddressState.ptrGetAlloc,Pointer.new,Size.ofBytes,resolved,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  simp only [Pointer.new] at pointer
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,pointer,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]
end DuplicatePrefix.WildcardUnexposedInteriorAddress
