import duplicate_prefix.GenericCallReturn
import duplicate_prefix.GenericPopFrame
import duplicate_prefix.RootGenericBoolWrite
import duplicate_prefix.RootPointerCopy

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PrimitiveCallReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem copy_usize_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (n : UInt64)
    (valid : localId < caller.locals.size)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some RootCompilerFacts.usizeLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout) :
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyReturn ()
      ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))), RootCompilerFacts.usizeLayout⟩ view
      (Storage.withCurrent frames caller machine) =
      (Storage.withCurrent frames {caller with locals := (caller.locals.set localId
        {value := .live (.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n)))),
         layout := caller.locals[localId].layout} valid)} machine, .ok ()) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let bound := ExecutionMachine.withValidation config limits
  let place := (ExecutionMachine.projectionHooks bound).place
  let dest := LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.usizeLayout
  let value : Immediate Provenance := Immediate.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have compatible : bound.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have flag := GenericCallReturn.same_layout_transmute_flag place bound.copy PreparedReflection.actual.compiler ()
    RootCompilerFacts.usizeLayout value dest rfl compatible
  have exactCopy : copyRuntimePlace place bound.copy () ⟨.immediate value, RootCompilerFacts.usizeLayout⟩ dest true =
      (ExecutionMachine.rvalueHooks config limits).copyOp () ⟨.immediate value, RootCompilerFacts.usizeLayout⟩ dest := by
    rw [flag]
    rfl
  have copy := ActualScalarCopy.actual_copy_usize options limits (remaining + 1) span debugOff n dest rfl
  have write := RootUsizeWrite.write_usize_shallow options limits remaining span debugOff fuel validationFuel
    frames caller machine localId old (ScalarInt.ofUInt64 n) valid live cached noClocks ghost shallow
  change MachineHooks.run (copyRuntimePlace place bound.copy ()
    ⟨.immediate value, RootCompilerFacts.usizeLayout⟩ view.toRuntimePlace true) _ = _
  rw [destination, exactCopy, copy]
  unfold MachineHooks.run Call.run
  rw [write]


theorem copy_bool_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (boolean : Bool)
    (valid : localId < caller.locals.size)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some RootCompilerFacts.boolLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.boolLayout) :
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyReturn ()
      ⟨.immediate (.scalar (Scalar.fromBool boolean)), RootCompilerFacts.boolLayout⟩ view
      (Storage.withCurrent frames caller machine) =
      (Storage.withCurrent frames {caller with locals := (caller.locals.set localId
        {value := .live (.immediate (.scalar (Scalar.fromBool boolean))),
         layout := caller.locals[localId].layout} valid)} machine, .ok ()) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let bound := ExecutionMachine.withValidation config limits
  let place := (ExecutionMachine.projectionHooks bound).place
  let dest := LocalPlaces.localRuntimePlace frames.size caller localId RootCompilerFacts.boolLayout
  let value : Immediate Provenance := Immediate.scalar (Scalar.fromBool boolean)
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have compatible : bound.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have flag := GenericCallReturn.same_layout_transmute_flag place bound.copy PreparedReflection.actual.compiler ()
    RootCompilerFacts.boolLayout value dest rfl compatible
  have exactCopy : copyRuntimePlace place bound.copy () ⟨.immediate value, RootCompilerFacts.boolLayout⟩ dest true =
      (ExecutionMachine.rvalueHooks config limits).copyOp () ⟨.immediate value, RootCompilerFacts.boolLayout⟩ dest := by
    rw [flag]
    rfl
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists RootCompilerFacts.boolLayout
    RootGenericBoolWrite.bool_initialized
  have copy := ActualScalarCopy.actual_copy_scalar options limits (remaining + 1) span debugOff
    RootCompilerFacts.boolLayout value dest rfl _ repr RootGenericBoolWrite.bool_sized
  have write := RootGenericBoolWrite.write_bool_shallow options limits remaining span debugOff fuel validationFuel
    frames caller machine localId old boolean valid live cached noClocks ghost shallow
  change MachineHooks.run (copyRuntimePlace place bound.copy ()
    ⟨.immediate value, RootCompilerFacts.boolLayout⟩ view.toRuntimePlace true) _ = _
  rw [destination, exactCopy, copy]
  unfold MachineHooks.run Call.run
  rw [write]


theorem copy_mut_pointer_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (scalar : Scalar Provenance)
    (valid : localId < caller.locals.size)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some CopyCompilerFacts.destPointerLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller localId CopyCompilerFacts.destPointerLayout) :
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyReturn ()
      ⟨.immediate (.scalar (scalar)), CopyCompilerFacts.destPointerLayout⟩ view
      (Storage.withCurrent frames caller machine) =
      (Storage.withCurrent frames {caller with locals := (caller.locals.set localId
        {value := .live (.immediate (.scalar (scalar))),
         layout := caller.locals[localId].layout} valid)} machine, .ok ()) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let bound := ExecutionMachine.withValidation config limits
  let place := (ExecutionMachine.projectionHooks bound).place
  let dest := LocalPlaces.localRuntimePlace frames.size caller localId CopyCompilerFacts.destPointerLayout
  let value : Immediate Provenance := Immediate.scalar (scalar)
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have compatible : bound.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have flag := GenericCallReturn.same_layout_transmute_flag place bound.copy PreparedReflection.actual.compiler ()
    CopyCompilerFacts.destPointerLayout value dest rfl compatible
  have exactCopy : copyRuntimePlace place bound.copy () ⟨.immediate value, CopyCompilerFacts.destPointerLayout⟩ dest true =
      (ExecutionMachine.rvalueHooks config limits).copyOp () ⟨.immediate value, CopyCompilerFacts.destPointerLayout⟩ dest := by
    rw [flag]
    rfl
  have copyBody := RootPointerCopy.copy_mut_pointer_shallow options limits remaining span debugOff fuel validationFuel
    frames caller machine localId old scalar valid live cached noClocks ghost shallow
  change MachineHooks.run (copyRuntimePlace place bound.copy ()
    ⟨.immediate value, CopyCompilerFacts.destPointerLayout⟩ view.toRuntimePlace true) _ = _
  rw [destination, exactCopy]
  unfold MachineHooks.run Call.run
  rw [copyBody]


theorem copy_const_pointer_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (scalar : Scalar Provenance)
    (valid : localId < caller.locals.size)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some CopyCompilerFacts.sourcePointerLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller localId CopyCompilerFacts.sourcePointerLayout) :
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyReturn ()
      ⟨.immediate (.scalar (scalar)), CopyCompilerFacts.sourcePointerLayout⟩ view
      (Storage.withCurrent frames caller machine) =
      (Storage.withCurrent frames {caller with locals := (caller.locals.set localId
        {value := .live (.immediate (.scalar (scalar))),
         layout := caller.locals[localId].layout} valid)} machine, .ok ()) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let bound := ExecutionMachine.withValidation config limits
  let place := (ExecutionMachine.projectionHooks bound).place
  let dest := LocalPlaces.localRuntimePlace frames.size caller localId CopyCompilerFacts.sourcePointerLayout
  let value : Immediate Provenance := Immediate.scalar (scalar)
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have compatible : bound.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have flag := GenericCallReturn.same_layout_transmute_flag place bound.copy PreparedReflection.actual.compiler ()
    CopyCompilerFacts.sourcePointerLayout value dest rfl compatible
  have exactCopy : copyRuntimePlace place bound.copy () ⟨.immediate value, CopyCompilerFacts.sourcePointerLayout⟩ dest true =
      (ExecutionMachine.rvalueHooks config limits).copyOp () ⟨.immediate value, CopyCompilerFacts.sourcePointerLayout⟩ dest := by
    rw [flag]
    rfl
  have copyBody := RootPointerCopy.copy_const_pointer_shallow options limits remaining span debugOff fuel validationFuel
    frames caller machine localId old scalar valid live cached noClocks ghost shallow
  change MachineHooks.run (copyRuntimePlace place bound.copy ()
    ⟨.immediate value, CopyCompilerFacts.sourcePointerLayout⟩ view.toRuntimePlace true) _ = _
  rw [destination, exactCopy]
  unfold MachineHooks.run Call.run
  rw [copyBody]


/-- Production returnOperand reads the cached immediate local0 through its
actual ghost-aware projection dictionary. -/
theorem read_current_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (layout : LocalLayout) (value : Immediate Provenance)
    (valid : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (live : frame.locals[0].value = .live (.immediate value))
    (cached : frame.locals[0].layout = some layout)
    (sized : layout.layout.isSized = true)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () remaining span) limits).returnOperand ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames frame machine, .ok ⟨.immediate value, layout⟩) := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  change MachineHooks.run (config.projection.place.localToOp () 0) _ = _
  rw [fields.projectionLocalToOp]
  have read := GenericCallReturn.cached_local_read (ValidityMachine.compilerPolicy config.compiler) ()
    frames frame machine 0 layout value valid live cached sized noClocks rfl ghost
  unfold MachineHooks.run Call.run
  rw [read]


/-- Actual canonical detached-frame cleanup for a normal helper containing
only immediate/dead local slots. -/
theorem cleanup_immediate_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (choice : Unit) (state : MachineHooks.State MiriMemoryKind Machine.RootUser)
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (ret : Option BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto ret unwindAction)
    (locals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[]) :
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () remaining span) limits).cleanupFrame
      choice false frame state = (state, .ok .normal) := by
  let config := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨unwind, afterPop⟩ := fields.lifecycleAfterPop
  have cleanup := GenericCallReturn.cleanup_immediate_frame_from_after_pop config.lifecycle unwind afterPop
    choice frame ret unwindAction continuation locals varargs
  change MachineHooks.run (CallMachine.cleanup config.lifecycle choice false frame) state = _
  rw [cleanup]
  rfl


/-- Actual canonical raw-pop callback for an immediate-only helper with no
owned protectors, including the source relevance-cache update before removal. -/
theorem pop_empty_current
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread) :
    (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () remaining span) limits).popFrame ()
      (Storage.withCurrent frames frame machine) =
      (⟨⟨frames⟩, GenericPopFrame.afterRelevanceAt frames frame machine
        (thread.topUserRelevantFrame.getD frames.size)⟩, .ok frame) := by
  let config := PreparedContracts.actualConfig options () remaining span
  have popped := GenericPopFrame.pop_empty_active (TypedMachineBindings.retagHooks config.access config.retag)
    frames frame machine tracker borrowFrame tracked frameTracked empty thread active
  change MachineHooks.run (TypedMachineBindings.popRaw
    (TypedMachineBindings.retagHooks config.access config.retag)) _ = _
  unfold MachineHooks.run Call.run
  rw [popped]


#print axioms copy_usize_return
#print axioms copy_bool_return
open Lean Elab Command in
run_cmd do
  for declaration in [``pop_empty_current, ``copy_mut_pointer_return, ``copy_const_pointer_return, ``cleanup_immediate_return, ``read_current_return, ``copy_usize_return, ``copy_bool_return] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.PrimitiveCallReturn
