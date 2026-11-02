import Miri.Interpreter.GlobalAllocationMachine
import Miri.Interpreter.TypedRetag
import Miri.Interpreter.ValidityMachine
import Miri.Interpreter.TypedValidityProviders

namespace EmptyFunction.UnitProtection
open Miri Miri.ABI Miri.Memory Miri.Interpreter
set_option autoImplicit false

/-- A live backing allocation needs no materialization. This is derived from
raw lookup and the canonical memory synchronization dictionary, rather than
assuming that ensure succeeds. -/
theorem ensure_live {K U : Type} [DecidableEq K] (kind : K)
    (hooks : GlobalAllocationHooks Provenance TreeBorrows.BorrowTree K
      (PlaceMachine.AccessState K U))
    (synchronize : ∀ memory view, hooks.synchronizeMemory memory view =
      {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (id : AllocId)
    (entry : LocalAllocation Provenance TreeBorrows.BorrowTree K)
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    GlobalAllocationMachine.ensure kind hooks id state = .ok () state := by
  change (let result := (MemoryLifecycle.getAllocRaw state.machine.memory
      (⟨state.machine, none⟩ : PlaceMachine.AccessState K U) id (some kind) hooks);
    (show MachineHooks.M K U Unit from do
      modify fun current => {current with machine := {result.hooks.machine with memory := result.memory}}
      match result.outcome with
      | .ok _ => pure ()
      | .error error => throw (result.hooks.pendingError.getD
          (.callback s!"global allocation access: {reprStr error}"))) state) = .ok () state
  simp [MemoryLifecycle.getAllocRaw, live, synchronize]
  with_unfolding_all rfl

/-- Zero-byte protection's preliminary access check performs no memory
operation, independently of pointer representation and runtime state. -/
theorem check_pointer_zero {K U : Type} (access : ValidityMachine.Access K U)
    (pointer : Pointer (Option Provenance)) (state : ValidityMachine.State K U) :
    ValidityMachine.checkPointerAccess access pointer Size.ZERO state = .ok () state := by
  with_unfolding_all rfl

/-- Concrete zero-size resolution uses the original cached base and preserves
state. The arithmetic law is an independently stated target-width property. -/
theorem resolve_concrete {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (id : AllocId) (tag : BorTag) (address base : UInt64)
    (truncate : ∀ value, pointers.arithmetic.truncateToTargetUsize value = .ok value)
    (state : ValidityMachine.State K U)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id,base⟩) :
    TypedValidityProviders.resolveAllocation pointers
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes address)) state =
      .ok (some ⟨id, Size.ofBytes (address-base), .concrete tag⟩) state := by
  have raw : state.machine.user.addresses.ptrGetAlloc
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) 0
      { sizeOf := fun id => (state.machine.memory.getAllocInfo id).toOption.map (·.size),
        isLive := fun id => some (state.machine.memory.isAllocLive id) }
      pointers.arithmetic = .ok (some (id,Size.ofBytes (address-base))) := by
    unfold AllocAddresses.GlobalAddressState.ptrGetAlloc
    change (show Except AllocAddresses.AddressStateError (Option (AllocId × Size)) from do
      let some b := (state.machine.user.addresses.baseAddr.find? (fun (row : AllocAddresses.BaseAddressEntry) => row.allocId == id)).map AllocAddresses.BaseAddressEntry.address
        | throw (.missingBaseAddress id)
      let relative ← (pointers.arithmetic.truncateToTargetUsize (address-b)).mapError AllocAddresses.AddressStateError.pointerArithmetic
      pure (some (id,Size.ofBytes relative))) = _
    simp [cached, truncate, Except.mapError]
    with_unfolding_all rfl
  unfold TypedValidityProviders.resolveAllocation
  change (let result := (PointerMachine.resolvePointer pointers state.machine.memory state
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes address)) 0);
    (show ValidityMachine.M K U (Option TreeBorrows.RetagPipeline.ResolvedLocation) from do
      set result.state
      match result.outcome with
      | .error error => throw (.callback error)
      | .ok (.error _) => pure none
      | .ok (.ok resolved) => pure (some ⟨resolved.allocId,resolved.offset,
          match resolved.extra with | .concrete _ tag => .concrete tag | .wildcard => .wildcard⟩)) state) = _
  simp only [Pointer.new] at raw
  simp [PointerMachine.resolvePointer, Pointer.new, raw]
  with_unfolding_all rfl

/-- The actual scoped uninitialization writer preserves arbitrary current ghost
mode and every machine/stack field for an aligned unit destination. -/
theorem scoped_uninit {K U : Type} [DecidableEq K]
    (access : ValidityMachine.Access K U) (place : MPlaceTy Provenance)
    (pointer : Pointer (Option Provenance)) (ty : Option Nat) (pointerSize : Size)
    (unitLayout : localMemoryLayout place.layout = ⟨Size.ZERO,Align.ONE,.Memory (sized := true),ty⟩)
    (encoding : place.mplace = ⟨pointer,.none,none⟩)
    (target : access.runtime.pointerSizeIn access.runtime.defaultAddressSpace = .ok pointerSize)
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (state : ValidityMachine.State K U) :
    (do
      let currentAccess ← ValidityMachine.scopedAccess access
      PlaceMachine.writeMemory currentAccess (fun _ => false) .uninit place) state = .ok () state := by
  have written := PlaceMachine.writeMemory_zero_uninit
    {access with ghostMode := state.machine.user.payload.ghost} (fun _ => false)
    place pointer ty pointerSize unitLayout encoding target retain state
  simpa only [ValidityMachine.scopedAccess,ValidityMachine.validationInProgress,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure] using written

/-- Address-only unit pointers need no allocation resolution or backing. -/
theorem resolve_integer {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (pointer : Pointer (Option Provenance)) (encoding : pointer.provenance = none)
    (state : ValidityMachine.State K U) :
    TypedValidityProviders.resolveAllocation pointers pointer state = .ok none state := by
  unfold TypedValidityProviders.resolveAllocation
  simp [PointerMachine.resolvePointer,encoding,get,getThe,MonadStateOf.get,EStateM.get,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,set,MonadStateOf.set,EStateM.set]
  rfl

end EmptyFunction.UnitProtection
