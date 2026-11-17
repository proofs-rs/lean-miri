import duplicate_prefix.AsMutPtrValidity
import duplicate_prefix.RootPointerCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.AsMutPtrWrites
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
theorem write_mut_slice_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (pointer : Pointer Provenance) (len : UInt64)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some AsMutPtrFacts.rawLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeImmediate
      () ((RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm)
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId AsMutPtrFacts.rawLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate ((RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm)), layout := frame.locals[localId].layout} valid)} machine) := by
  apply RootPointerWrite.write_validated_local options limits remaining span debugOff fuel validationFuel framesBefore frame machine
    localId old AsMutPtrFacts.rawLayout ((RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm) valid live cached noClocks ghostFalse shallow (by with_unfolding_all rfl)
  intro postFrame postValid postLive postCached
  exact AsMutPtrValidity.validate_mut_slice_shallow options remaining span debugOff fuel framesBefore postFrame machine localId pointer len
    postValid postLive postCached ghostFalse shallow

theorem write_integer_mut_slice_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (address len : UInt64)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some AsMutPtrFacts.rawLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeImmediate
      () ((RetagReferencePlace.integerSliceValue address len AsMutPtrFacts.rawLayout).imm)
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId AsMutPtrFacts.rawLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate ((RetagReferencePlace.integerSliceValue address len AsMutPtrFacts.rawLayout).imm)), layout := frame.locals[localId].layout} valid)} machine) := by
  apply RootPointerWrite.write_validated_local options limits remaining span debugOff fuel validationFuel framesBefore frame machine
    localId old AsMutPtrFacts.rawLayout ((RetagReferencePlace.integerSliceValue address len AsMutPtrFacts.rawLayout).imm) valid live cached noClocks ghostFalse shallow (by with_unfolding_all rfl)
  intro postFrame postValid postLive postCached
  exact AsMutPtrValidity.validate_integer_mut_slice_shallow options remaining span debugOff fuel framesBefore postFrame machine localId address len
    postValid postLive postCached ghostFalse shallow

theorem copy_mut_slice_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (pointer : Pointer Provenance) (len : UInt64)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some AsMutPtrFacts.rawLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyOp
      () ⟨.immediate ((RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm), AsMutPtrFacts.rawLayout⟩
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId AsMutPtrFacts.rawLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate ((RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm)), layout := frame.locals[localId].layout} valid)} machine) := by
  rw [ActualScalarCopy.actual_copy_no_padding options limits (remaining + 1) span debugOff
    AsMutPtrFacts.rawLayout ((RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len AsMutPtrFacts.rawLayout).imm) _ rfl AsMutPtrFacts.raw_no_padding AsMutPtrFacts.raw_sized]
  exact write_mut_slice_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine localId old pointer len valid live cached noClocks ghostFalse shallow

theorem copy_integer_mut_slice_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (address len : UInt64)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some AsMutPtrFacts.rawLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyOp
      () ⟨.immediate ((RetagReferencePlace.integerSliceValue address len AsMutPtrFacts.rawLayout).imm), AsMutPtrFacts.rawLayout⟩
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId AsMutPtrFacts.rawLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate ((RetagReferencePlace.integerSliceValue address len AsMutPtrFacts.rawLayout).imm)), layout := frame.locals[localId].layout} valid)} machine) := by
  rw [ActualScalarCopy.actual_copy_no_padding options limits (remaining + 1) span debugOff
    AsMutPtrFacts.rawLayout ((RetagReferencePlace.integerSliceValue address len AsMutPtrFacts.rawLayout).imm) _ rfl AsMutPtrFacts.raw_no_padding AsMutPtrFacts.raw_sized]
  exact write_integer_mut_slice_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine localId old address len valid live cached noClocks ghostFalse shallow

open Lean Elab Command in
run_cmd do
  for declaration in [``write_mut_slice_shallow, ``write_integer_mut_slice_shallow,
      ``copy_mut_slice_shallow, ``copy_integer_mut_slice_shallow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.AsMutPtrWrites
