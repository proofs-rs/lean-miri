import duplicate_prefix.S04ReturnGhostRead
import duplicate_prefix.S04ReturnGhostClear
import duplicate_prefix.S04ReturnPrimitiveValidity
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04ReturnBoolValidation
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
abbrev ghostState (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :=
  {state with machine := {state.machine with user := {state.machine.user with
    payload := {state.machine.user.payload with ghost := true}}}}
theorem validate_on_context (context : PhysicalMachineWrite.Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (mplace : MemPlace Provenance) (id : AllocId) (provenance : Provenance) (extra : ProvenanceExtra) (base offset capacity : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (updated : Allocation Provenance BorrowTree) (value : Bool) (hooks : ValidityVisitor.Hooks Provenance (MachineHooks.State MiriMemoryKind Machine.RootUser) Unit MachineHooks.FrameExtra F A Pad)
    (placeHooks : PlaceHooks Provenance (MachineHooks.State MiriMemoryKind Machine.RootUser) Unit MachineHooks.FrameExtra)
    (choice : Unit) (fuel : Nat) (name : String)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes capacity)
    (bounds : offset.toNat+1≤capacity.toNat)
    (mutable : entry.allocation.mutability = .Mut)
    (scalarRead : Allocation.readScalar entry.allocation context.access.runtime.base
      (allocRange (Size.ofBytes offset) (Size.ofBytes 1)) false = .ok (Scalar.fromBool value))
    (mutation : Allocation.clearProvenance (allocRange (Size.ofBytes offset) (Size.ofBytes 1))
      (Size.ofBytes 8) entry.allocation = .ok () updated)
    (pointer : mplace.ptr = Pointer.new (some provenance) (Size.ofBytes (base+offset)))
    (aligned : mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (resolved : context.access.resolvePointer (ghostState state).machine.memory
      (Pointer.new (some provenance) (Size.ofBytes (base+offset))) (Int.ofNat (1 : UInt64).toNat)
      (ghostState state).machine =
      .ok (.ok ⟨id,Size.ofBytes offset,extra⟩) (ghostState state).machine)
    (ghost : state.machine.user.payload.ghost = false)
    (named : hooks.typeName choice RootCompilerFacts.boolLayout.ty = pure name)
    (classified : hooks.classify choice RootCompilerFacts.boolLayout.ty = pure .boolean)
    (toOpField : hooks.toOp = fun c place => placeToOp placeHooks c place)
    (readField : hooks.readImmediate = fun c place expected => do
      let op ← placeToOp placeHooks c place
      ValidityMemory.readImmediate (ValidityMachine.memoryEnvironment context.access) op expected)
    (clearField : hooks.clearProvenance = fun c place =>
      ValidityMemory.clearPlaceProvenance (ValidityMachine.memoryEnvironment context.access) placeHooks c
        ValidityMachine.validationInProgress MachineHooks.afterLocalWrite place)
    (ghostField : hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
      @ValidityMachine.withGhostValidation MiriMemoryKind _ (ValidityVisitor.Session Provenance))
    (sizing : hooks.sizeAndAlign choice ⟨mplace,RootCompilerFacts.boolLayout⟩ =
      pure (some (Size.ofBytes 1,Align.ONE)))
    (finish : Size) (endpoint : (allocRange mplace.ptr.offset (Size.ofBytes 1)).endExclusive = .ok finish) :
    ValidityVisitor.validatePlace hooks choice (fuel + 1) ⟨.memory mplace,RootCompilerFacts.boolLayout⟩ false true state =
      .ok () (CanonicalCopy.replaceAllocation state id entry.kind updated) := by
  let active := ghostState state
  let after := CanonicalCopy.replaceAllocation state id entry.kind updated
  let activeAfter := ghostState after
  have operand : hooks.toOp choice ⟨.memory mplace,RootCompilerFacts.boolLayout⟩ active =
      .ok ⟨.indirect mplace,RootCompilerFacts.boolLayout⟩ active := by
    rw [toOpField]
    rfl
  have read : hooks.readImmediate choice ⟨.memory mplace,RootCompilerFacts.boolLayout⟩ .boolean active =
      .ok ⟨.scalar (Scalar.fromBool value),RootCompilerFacts.boolLayout⟩ active := by
    rw [readField]
    simp only [placeToOp, placeToOpCore, bind, EStateM.bind, pure, EStateM.pure]
    exact S04ReturnGhostRead.validity_bool_on_context context active mplace id provenance extra base offset capacity entry value .boolean
      width cached present size bounds mutable scalarRead pointer aligned runtimeSize resolved
  have clear : hooks.clearProvenance choice ⟨.memory mplace,RootCompilerFacts.boolLayout⟩ active = .ok () activeAfter := by
    rw [clearField]
    have actual := S04ReturnGhostClear.clear_on_context_ghost context active mplace id provenance extra base offset capacity
      entry updated placeHooks choice width cached present size bounds mutable mutation pointer aligned runtimeSize resolved
    exact actual
  have operandAfter : hooks.toOp choice ⟨.memory mplace,RootCompilerFacts.boolLayout⟩ activeAfter =
      .ok ⟨.indirect mplace,RootCompilerFacts.boolLayout⟩ activeAfter := by
    rw [toOpField]
    rfl
  have classification : hooks.classify choice RootCompilerFacts.boolLayout.ty active = .ok .boolean active := by
    rw [classified]; rfl
  have actualSize : hooks.sizeAndAlign choice ⟨mplace,RootCompilerFacts.boolLayout⟩ activeAfter =
      .ok (some (RootCompilerFacts.boolLayout.layout.size,RootCompilerFacts.boolLayout.layout.align.abi)) activeAfter := by
    rw [sizing]
    rfl
  exact S04ReturnPrimitiveValidity.validate_boolean_memory hooks choice fuel state after ghost
    mplace RootCompilerFacts.boolLayout value name ghost named ghostField active rfl activeAfter rfl operandAfter
    classification read clear operand actualSize (by decide +kernel) (by decide +kernel) finish endpoint
end DuplicatePrefix.S04ReturnBoolValidation
