import duplicate_prefix.PrimitiveArgumentCopy
import duplicate_prefix.RootPointerCopy
namespace DuplicatePrefix.PointerArgumentCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem copy_mut_pointer_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (pointer : Scalar Provenance)
    (valid : localId < caller.locals.size)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some CopyCompilerFacts.destPointerLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller localId CopyCompilerFacts.destPointerLayout) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (.scalar pointer), CopyCompilerFacts.destPointerLayout⟩ view
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent frames {caller with locals := (caller.locals.set localId
        {value := .live (.immediate (.scalar pointer)),
         layout := caller.locals[localId].layout} valid)} machine) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let bound := ExecutionMachine.withValidation config limits
  let place := (ExecutionMachine.projectionHooks bound).place
  let dest := LocalPlaces.localRuntimePlace frames.size caller localId CopyCompilerFacts.destPointerLayout
  let value : Immediate Provenance := Immediate.scalar pointer
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
  have copy := RootPointerCopy.copy_mut_pointer_shallow options limits remaining span debugOff fuel validationFuel
    frames caller machine localId old pointer valid live cached noClocks ghost shallow
  change copyRuntimePlace place bound.copy ()
    ⟨.immediate value, CopyCompilerFacts.destPointerLayout⟩ view.toRuntimePlace true _ = _
  rw [destination, exactCopy]
  exact copy


theorem copy_const_pointer_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (pointer : Scalar Provenance)
    (valid : localId < caller.locals.size)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some CopyCompilerFacts.sourcePointerLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller localId CopyCompilerFacts.sourcePointerLayout) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (.scalar pointer), CopyCompilerFacts.sourcePointerLayout⟩ view
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent frames {caller with locals := (caller.locals.set localId
        {value := .live (.immediate (.scalar pointer)),
         layout := caller.locals[localId].layout} valid)} machine) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let bound := ExecutionMachine.withValidation config limits
  let place := (ExecutionMachine.projectionHooks bound).place
  let dest := LocalPlaces.localRuntimePlace frames.size caller localId CopyCompilerFacts.sourcePointerLayout
  let value : Immediate Provenance := Immediate.scalar pointer
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
  have copy := RootPointerCopy.copy_const_pointer_shallow options limits remaining span debugOff fuel validationFuel
    frames caller machine localId old pointer valid live cached noClocks ghost shallow
  change copyRuntimePlace place bound.copy ()
    ⟨.immediate value, CopyCompilerFacts.sourcePointerLayout⟩ view.toRuntimePlace true _ = _
  rw [destination, exactCopy]
  exact copy


open Lean Elab Command in
run_cmd do
  for declaration in [``copy_mut_pointer_argument, ``copy_const_pointer_argument] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved raw pointer argument copy {dependency}"
end DuplicatePrefix.PointerArgumentCopy
