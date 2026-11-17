import duplicate_prefix.PrimitiveCallReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.PrimitiveArgumentCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
theorem copy_usize_argument
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
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyAllowTransmute ()
      ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n))), RootCompilerFacts.usizeLayout⟩ view
      (Storage.withCurrent frames caller machine) =
      .ok () (Storage.withCurrent frames {caller with locals := (caller.locals.set localId
        {value := .live (.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 n)))),
         layout := caller.locals[localId].layout} valid)} machine) := by
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
  change copyRuntimePlace place bound.copy ()
    ⟨.immediate value, RootCompilerFacts.usizeLayout⟩ view.toRuntimePlace true _ = _
  rw [destination, exactCopy, copy]
  exact write


#print axioms copy_usize_argument
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``copy_usize_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved primitive argument dependency {dependency}"
end DuplicatePrefix.PrimitiveArgumentCopy
