import duplicate_prefix.PrimitiveCallReturn
import duplicate_prefix.RootPointerCopy
import duplicate_prefix.PtrMetadataComplete
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.RawArgumentCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
theorem copy_raw_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (caller : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (carrier : Pointer Provenance ⊕ UInt64) (len : UInt64)
    (valid : localId < caller.locals.size)
    (live : caller.locals[localId].value = .live (.immediate old))
    (cached : caller.locals[localId].layout = some PtrMetadataHelper.rawLayout)
    (noClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller localId PtrMetadataHelper.rawLayout) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len), PtrMetadataHelper.rawLayout⟩ view
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent frames {caller with locals := (caller.locals.set localId
        {value := .live (.immediate (PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)),
         layout := caller.locals[localId].layout} valid)} machine) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let bound := ExecutionMachine.withValidation config limits
  let place := (ExecutionMachine.projectionHooks bound).place
  let dest := LocalPlaces.localRuntimePlace frames.size caller localId PtrMetadataHelper.rawLayout
  let value : Immediate Provenance := PtrMetadataComplete.rawImmediate carrier (PreparedContracts.actualConfig options () remaining span).access.runtime.base len
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have compatible : bound.copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have flag := GenericCallReturn.same_layout_transmute_flag place bound.copy PreparedReflection.actual.compiler ()
    PtrMetadataHelper.rawLayout value dest rfl compatible
  have exactCopy : copyRuntimePlace place bound.copy () ⟨.immediate value, PtrMetadataHelper.rawLayout⟩ dest true =
      (ExecutionMachine.rvalueHooks config limits).copyOp () ⟨.immediate value, PtrMetadataHelper.rawLayout⟩ dest := by
    rw [flag]
    rfl
  change copyRuntimePlace place bound.copy ()
    ⟨.immediate value, PtrMetadataHelper.rawLayout⟩ view.toRuntimePlace true _ = _
  rw [destination, exactCopy]
  cases carrier with
  | inl pointer =>
    exact RootPointerCopy.copy_raw_slice_shallow options limits remaining span debugOff fuel validationFuel
      frames caller machine localId old pointer len valid live cached noClocks ghost shallow
  | inr address =>
    exact RootPointerCopy.copy_integer_slice_shallow options limits remaining span debugOff fuel validationFuel
      frames caller machine localId old address len valid live cached noClocks ghost shallow



end DuplicatePrefix.RawArgumentCopy
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.RawArgumentCopy.copy_raw_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved raw argument dependency {dependency}"
