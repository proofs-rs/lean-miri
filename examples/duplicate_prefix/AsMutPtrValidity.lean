import duplicate_prefix.AsMutPtrFacts
import duplicate_prefix.FatRawPointerValidity
import duplicate_prefix.RootRawPointerValidity
import duplicate_prefix.WideValidityQueries
import duplicate_prefix.PtrMetadataHelper
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.AsMutPtrValidity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open RootPrimitiveValidation
theorem validate_mut_slice_shallow
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (pointer : Pointer Provenance) (len : UInt64)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalarPair (Scalar.fromPointer (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer)
      (Scalar.fromScalarInt (ScalarInt.ofUInt64 len)))))
    (cached : frame.locals[localId].layout = some AsMutPtrFacts.rawLayout)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
 :
    ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity
      () (fuel + 1) (LocalPlaces.localRuntimePlace framesBefore.size frame localId AsMutPtrFacts.rawLayout) true
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  let inner := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, vtable, discriminant, validityField⟩ := fields.validity
  let queries := CompilerValidityLeaves.make PreparedReflection.actual.compiler
    PreparedReflection.actual.image EvalProjectionMachine.arrays inner.projection pointers
  let base := ExecutionValidity.hooks queries inner.access inner.allocation inner.compiler
    inner.projection vtable discriminant inner.retag options.limits.retag
  let hooks := TypedValidityProviders.visitor
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime inner.access inner.allocation
    inner.compiler pointers inner.retag options.limits.retag base
  have hooksEq : inner.validity = hooks := by rw [validityField]; rfl
  let layout := AsMutPtrFacts.rawLayout
  let pointee := PtrMetadataHelper.sliceLayout
  let first := Scalar.fromPointer inner.access.runtime.base pointer
  let second : Scalar Provenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 len)
  obtain ⟨typedCompiler, typedDebug, typedNoDebug, toOpField, readField, writeField, ptrField,
      tailField, targetField, ghostField, classifyField, nameField⟩ := ScalarCopyStage.typed_visitor_wide_pointer_fields
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime base inner.access inner.allocation inner.compiler
    pointers inner.retag options.limits.retag
  have debug : typedCompiler.debugAssertions = false := by rw [typedDebug, fields.debug, debugOff]
  have noDebug : typedCompiler.debugAbiCheck (.scalarPair first second) layout = pure () := by
    rw [typedNoDebug, fields.debugAbiNoChecks debugOff]
  have retain := CanonicalConfigFacts.actual_retain_touched options () remaining span
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent framesBefore frame activeMachine
  have kindQuery : hooks.classify () layout.ty active = .ok (.rawPointer 4 false) active := by
    rw [classifyField]
    change (CompilerFactAdapters.validityHooks _ base).classify () AsMutPtrFacts.rawLayout.ty active = _
    rw [AsMutPtrFacts.raw_type, AsMutPtrFacts.hooks_raw_slice_kind]
    rfl
  have nameQuery : hooks.typeName () layout.ty = pure "*mut [u8]" := by
    rw [nameField]
    change (CompilerFactAdapters.validityHooks _ base).typeName () AsMutPtrFacts.rawLayout.ty = _
    rw [AsMutPtrFacts.raw_type, AsMutPtrFacts.hooks_raw_slice_name]
  have targetQuery : hooks.ptrToPlace () ⟨.scalarPair first second, layout⟩ =
      pure (RetagReferencePlace.slicePlace pointer len pointee) := by
    rw [ptrField]
    exact RetagReferencePlace.from_immediate inner.access _ () pointer len layout pointee
      (by
        change (CompilerExecutionProviders.pointerCompiler _).builtinDeref () AsMutPtrFacts.rawLayout.ty = pure (some PtrMetadataHelper.sliceLayout.ty)
        rw [AsMutPtrFacts.raw_type, PtrMetadataHelper.slice_layout_type]
        exact AsMutPtrFacts.compiler_raw_deref ())
      (by
        change (CompilerExecutionProviders.pointerCompiler _).layoutOf () PtrMetadataHelper.sliceLayout.ty = pure PtrMetadataHelper.sliceLayout
        rw [PtrMetadataHelper.slice_layout_type]
        exact PtrMetadataHelper.compiler_slice_layout ())
      PtrMetadataHelper.slice_align
  have metadataQuery : source_check_metadata hooks ()
      (RetagReferencePlace.slicePlace pointer len pointee) = pure () := by
    apply ReferenceValidity.metadata_slice hooks () _ len
    · rw [tailField]
      change (CompilerFactAdapters.validityHooks _ base).metadataTail () PtrMetadataHelper.sliceLayout.ty = _
      rw [PtrMetadataHelper.slice_layout_type, WideValidityQueries.hooks_slice_metadata_tail]
    · rfl
    · rw [targetField]
      change inner.access.runtime.pointerSize = Size.ofBytes 8
      rw [fields.accessRuntime]
      rfl
  obtain ⟨pa, pb, ra, rb, offset, repr⟩ := AsMutPtrFacts.raw_readable
  have sized : layout.layout.isSized = true := by with_unfolding_all rfl
  have validator := FatRawPointerValidity.validate_fat_raw_pointer_fields_shallow hooks inner.access inner.allocation
    typedCompiler fuel () framesBefore frame machine localId layout first second
    valid live cached sized pa pb ra rb offset repr debug ghostFalse retain "*mut [u8]" 4
    (RetagReferencePlace.slicePlace pointer len pointee) PtrMetadataHelper.slice_unsized targetQuery metadataQuery
    nameQuery kindQuery toOpField readField noDebug writeField ghostField
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent framesBefore frame machine) =
      .ok false (Storage.withCurrent framesBefore frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively, Storage.withCurrent, shallow,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  change ValidityMachine.validateRuntime inner.validity () (fuel + 1) _ true _ = _
  rw [hooksEq]
  unfold ValidityMachine.validateRuntime
  simp only [bind, EStateM.bind, recursive]
  exact validator

theorem validate_integer_mut_slice_shallow
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (address len : UInt64)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalarPair (Scalar.fromScalarInt (ScalarInt.ofUInt64 address))
      (Scalar.fromScalarInt (ScalarInt.ofUInt64 len)))))
    (cached : frame.locals[localId].layout = some AsMutPtrFacts.rawLayout)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
 :
    ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity
      () (fuel + 1) (LocalPlaces.localRuntimePlace framesBefore.size frame localId AsMutPtrFacts.rawLayout) true
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  let inner := PreparedContracts.actualConfig options () remaining span
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  obtain ⟨pointers, vtable, discriminant, validityField⟩ := fields.validity
  let queries := CompilerValidityLeaves.make PreparedReflection.actual.compiler
    PreparedReflection.actual.image EvalProjectionMachine.arrays inner.projection pointers
  let base := ExecutionValidity.hooks queries inner.access inner.allocation inner.compiler
    inner.projection vtable discriminant inner.retag options.limits.retag
  let hooks := TypedValidityProviders.visitor
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime inner.access inner.allocation
    inner.compiler pointers inner.retag options.limits.retag base
  have hooksEq : inner.validity = hooks := by rw [validityField]; rfl
  let layout := AsMutPtrFacts.rawLayout
  let pointee := PtrMetadataHelper.sliceLayout
  let first : Scalar Provenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 address)
  let second : Scalar Provenance := Scalar.fromScalarInt (ScalarInt.ofUInt64 len)
  obtain ⟨typedCompiler, typedDebug, typedNoDebug, toOpField, readField, writeField, ptrField,
      tailField, targetField, ghostField, classifyField, nameField⟩ := ScalarCopyStage.typed_visitor_wide_pointer_fields
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime base inner.access inner.allocation inner.compiler
    pointers inner.retag options.limits.retag
  have debug : typedCompiler.debugAssertions = false := by rw [typedDebug, fields.debug, debugOff]
  have noDebug : typedCompiler.debugAbiCheck (.scalarPair first second) layout = pure () := by
    rw [typedNoDebug, fields.debugAbiNoChecks debugOff]
  have retain := CanonicalConfigFacts.actual_retain_touched options () remaining span
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent framesBefore frame activeMachine
  have kindQuery : hooks.classify () layout.ty active = .ok (.rawPointer 4 false) active := by
    rw [classifyField]
    change (CompilerFactAdapters.validityHooks _ base).classify () AsMutPtrFacts.rawLayout.ty active = _
    rw [AsMutPtrFacts.raw_type, AsMutPtrFacts.hooks_raw_slice_kind]
    rfl
  have nameQuery : hooks.typeName () layout.ty = pure "*mut [u8]" := by
    rw [nameField]
    change (CompilerFactAdapters.validityHooks _ base).typeName () AsMutPtrFacts.rawLayout.ty = _
    rw [AsMutPtrFacts.raw_type, AsMutPtrFacts.hooks_raw_slice_name]
  have targetQuery : hooks.ptrToPlace () ⟨.scalarPair first second, layout⟩ =
      pure (RetagReferencePlace.integerSlicePlace address len pointee) := by
    rw [ptrField]
    exact RetagReferencePlace.canonical_from_integer inner.access
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts () address len layout pointee
      (by
        change CompilerFacts.builtinDeref _ AsMutPtrFacts.rawLayout.ty true = .ok (some PtrMetadataHelper.sliceLayout.ty)
        rw [AsMutPtrFacts.raw_type, PtrMetadataHelper.slice_layout_type]
        exact AsMutPtrFacts.raw_builtin_deref)
      (by
        change CompilerFacts.layoutOf _ PtrMetadataHelper.sliceLayout.ty = .ok PtrMetadataHelper.sliceLayout
        rw [PtrMetadataHelper.slice_layout_type]
        exact PtrMetadataHelper.context_slice_layout)
      PtrMetadataHelper.slice_align
      (by rw [fields.accessRuntime]; rfl)

  have metadataQuery : source_check_metadata hooks ()
      (RetagReferencePlace.integerSlicePlace address len pointee) = pure () := by
    apply ReferenceValidity.metadata_slice hooks () _ len
    · rw [tailField]
      change (CompilerFactAdapters.validityHooks _ base).metadataTail () PtrMetadataHelper.sliceLayout.ty = _
      rw [PtrMetadataHelper.slice_layout_type, WideValidityQueries.hooks_slice_metadata_tail]
    · rfl
    · rw [targetField]
      change inner.access.runtime.pointerSize = Size.ofBytes 8
      rw [fields.accessRuntime]
      rfl
  obtain ⟨pa, pb, ra, rb, offset, repr⟩ := AsMutPtrFacts.raw_readable
  have sized : layout.layout.isSized = true := by with_unfolding_all rfl
  have validator := FatRawPointerValidity.validate_fat_raw_pointer_fields_shallow hooks inner.access inner.allocation
    typedCompiler fuel () framesBefore frame machine localId layout first second
    valid live cached sized pa pb ra rb offset repr debug ghostFalse retain "*mut [u8]" 4
    (RetagReferencePlace.integerSlicePlace address len pointee) PtrMetadataHelper.slice_unsized targetQuery metadataQuery
    nameQuery kindQuery toOpField readField noDebug writeField ghostField
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent framesBefore frame machine) =
      .ok false (Storage.withCurrent framesBefore frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively, Storage.withCurrent, shallow,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  change ValidityMachine.validateRuntime inner.validity () (fuel + 1) _ true _ = _
  rw [hooksEq]
  unfold ValidityMachine.validateRuntime
  simp only [bind, EStateM.bind, recursive]
  exact validator

#print axioms validate_mut_slice_shallow
open Lean Elab Command in
run_cmd do
  for declaration in [``validate_mut_slice_shallow, ``validate_integer_mut_slice_shallow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved axiom {dependency}"
end DuplicatePrefix.AsMutPtrValidity
