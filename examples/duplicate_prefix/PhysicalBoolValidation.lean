import duplicate_prefix.PhysicalPrimitiveValidity
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PhysicalBoolValidation
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.Input
open PhysicalMachineWrite
theorem validate_on_context (context : Context)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (mplace : MemPlace Provenance) (id : AllocId) (tag : BorTag) (base : UInt64)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (value : Bool) (hooks : ValidityVisitor.Hooks Provenance (MachineHooks.State MiriMemoryKind Machine.RootUser) Unit MachineHooks.FrameExtra F A Pad)
    (placeHooks : PlaceHooks Provenance (MachineHooks.State MiriMemoryKind Machine.RootUser) Unit MachineHooks.FrameExtra)
    (choice : Unit) (fuel : Nat) (name : String)
    (width : context.pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes 1)
    (mutable : entry.allocation.mutability = .Mut)
    (storage : entry.allocation.len = entry.allocation.byteSize.bytes.toNat)
    (mask : entry.allocation.initializationMask = InitMask.new entry.allocation.byteSize true)
    (encoding : target_bytes context.access.runtime.base entry.allocation.byteSize (if value then 1 else 0) =
      .ok (AllocationCopy.snapshot entry.allocation))
    (pointer : mplace.ptr = Pointer.new (some (.concrete id tag)) (Size.ofBytes base))
    (aligned : mplace.misaligned = none)
    (runtimeSize : context.access.runtime.pointerSize = Size.ofBytes 8)
    (emptyProvenance : entry.allocation.provenanceMap = ProvenanceMap.new)
    (canonicalHeap : (state.machine.memory.live.filter fun row => row.1 != id).push (id,entry) = state.machine.memory.live)
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
      .ok () state := by
  let active : MachineHooks.State MiriMemoryKind Machine.RootUser := {state with machine := {state.machine with
    user := {state.machine.user with payload := {state.machine.user.payload with ghost := true}}}}
  have operand : hooks.toOp choice ⟨.memory mplace,RootCompilerFacts.boolLayout⟩ active =
      .ok ⟨.indirect mplace,RootCompilerFacts.boolLayout⟩ active := by
    rw [toOpField]
    rfl
  have read : hooks.readImmediate choice ⟨.memory mplace,RootCompilerFacts.boolLayout⟩ .boolean active =
      .ok ⟨.scalar (Scalar.fromBool value),RootCompilerFacts.boolLayout⟩ active := by
    rw [readField]
    simp only [placeToOp, placeToOpCore, bind, EStateM.bind, pure, EStateM.pure]
    exact PhysicalMachineRead.validity_bool_on_context context active mplace id tag base entry value .boolean
      width cached present size mutable storage mask encoding pointer aligned runtimeSize
  have clear : hooks.clearProvenance choice ⟨.memory mplace,RootCompilerFacts.boolLayout⟩ active = .ok () active := by
    rw [clearField]
    have actual := PhysicalValidityMemory.clear_on_context_ghost context active mplace id tag base entry placeHooks choice
      width cached present size mutable storage emptyProvenance pointer aligned runtimeSize
    simpa only [active, canonicalHeap] using actual
  have classification : hooks.classify choice RootCompilerFacts.boolLayout.ty active = .ok .boolean active := by
    rw [classified]; rfl
  have actualSize : hooks.sizeAndAlign choice ⟨mplace,RootCompilerFacts.boolLayout⟩ active =
      .ok (some (RootCompilerFacts.boolLayout.layout.size,RootCompilerFacts.boolLayout.layout.align.abi)) active := by
    rw [sizing]
    rfl
  exact PhysicalPrimitiveValidity.validate_boolean_memory hooks choice fuel state mplace RootCompilerFacts.boolLayout value name
    ghost named ghostField active rfl classification read clear operand actualSize (by decide +kernel) (by decide +kernel)
    finish endpoint

#print axioms validate_on_context
end DuplicatePrefix.PhysicalBoolValidation
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.PhysicalBoolValidation.validate_on_context) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved physical bool validation dependency {dependency}"
