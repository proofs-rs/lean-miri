import duplicate_prefix.RootPointerWrite
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.RootPointerCopy
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

theorem raw_no_padding : CompilerCopy.hasPadding PreparedReflection.actual.compiler.runtime false
    PtrMetadataHelper.rawLayout = .ok false := by decide +kernel

theorem raw_sized : PtrMetadataHelper.rawLayout.layout.isSized = true := by with_unfolding_all rfl

theorem copy_mut_pointer_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (value : Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some CopyCompilerFacts.destPointerLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyOp
      () ⟨.immediate (.scalar value), CopyCompilerFacts.destPointerLayout⟩
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId CopyCompilerFacts.destPointerLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (.scalar value)), layout := frame.locals[localId].layout} valid)} machine) := by
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists CopyCompilerFacts.destPointerLayout CopyCompilerFacts.primitive_layouts_initialized.2.2.1
  rw [ActualScalarCopy.actual_copy_scalar options limits (remaining + 1) span debugOff
    CopyCompilerFacts.destPointerLayout (.scalar value) _ rfl _ repr RootRawPointerValidity.mut_pointer_sized]
  exact RootPointerWrite.write_mut_pointer_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine localId old value valid live cached noClocks ghostFalse shallow

theorem copy_const_pointer_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance) (value : Scalar Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some CopyCompilerFacts.sourcePointerLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyOp
      () ⟨.immediate (.scalar value), CopyCompilerFacts.sourcePointerLayout⟩
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId CopyCompilerFacts.sourcePointerLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate (.scalar value)), layout := frame.locals[localId].layout} valid)} machine) := by
  obtain ⟨primitive, range, repr⟩ := CopyCompilerFacts.initialized_scalar_exists CopyCompilerFacts.sourcePointerLayout CopyCompilerFacts.primitive_layouts_initialized.2.1
  rw [ActualScalarCopy.actual_copy_scalar options limits (remaining + 1) span debugOff
    CopyCompilerFacts.sourcePointerLayout (.scalar value) _ rfl _ repr RootRawPointerValidity.const_pointer_sized]
  exact RootPointerWrite.write_const_pointer_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine localId old value valid live cached noClocks ghostFalse shallow

theorem copy_raw_slice_shallow
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
    (cached : frame.locals[localId].layout = some PtrMetadataHelper.rawLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyOp
      () ⟨.immediate ((RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len PtrMetadataHelper.rawLayout).imm), PtrMetadataHelper.rawLayout⟩
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId PtrMetadataHelper.rawLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate ((RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len PtrMetadataHelper.rawLayout).imm)), layout := frame.locals[localId].layout} valid)} machine) := by
  rw [ActualScalarCopy.actual_copy_no_padding options limits (remaining + 1) span debugOff
    PtrMetadataHelper.rawLayout ((RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len PtrMetadataHelper.rawLayout).imm) _ rfl raw_no_padding raw_sized]
  exact RootPointerWrite.write_raw_slice_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine localId old pointer len valid live cached noClocks ghostFalse shallow

theorem copy_integer_slice_shallow
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
    (cached : frame.locals[localId].layout = some PtrMetadataHelper.rawLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyOp
      () ⟨.immediate ((RetagReferencePlace.integerSliceValue address len PtrMetadataHelper.rawLayout).imm), PtrMetadataHelper.rawLayout⟩
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId PtrMetadataHelper.rawLayout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate ((RetagReferencePlace.integerSliceValue address len PtrMetadataHelper.rawLayout).imm)), layout := frame.locals[localId].layout} valid)} machine) := by
  rw [ActualScalarCopy.actual_copy_no_padding options limits (remaining + 1) span debugOff
    PtrMetadataHelper.rawLayout ((RetagReferencePlace.integerSliceValue address len PtrMetadataHelper.rawLayout).imm) _ rfl raw_no_padding raw_sized]
  exact RootPointerWrite.write_integer_slice_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine localId old address len valid live cached noClocks ghostFalse shallow

open Lean Elab Command in
run_cmd do
  for declaration in [``raw_no_padding, ``raw_sized, ``copy_mut_pointer_shallow, ``copy_const_pointer_shallow,
      ``copy_raw_slice_shallow, ``copy_integer_slice_shallow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.RootPointerCopy
