import duplicate_prefix.ScalarCopyStage
import duplicate_prefix.CanonicalConfigFacts
import duplicate_prefix.ScalarValidityQueries
import Miri.Input.EvalValidityMachine

set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

namespace DuplicatePrefix.RootPrimitiveValidation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev BaseHooks := ValidityVisitor.Hooks Provenance CanonicalConfigFacts.RootState Unit
  MachineHooks.FrameExtra (FnVal Unit) (FnAbi TyId) ValidityMemory.PaddingHandle

theorem validate_nested_primitive_shallow
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (layout : LocalLayout) (bits : ScalarInt)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate (.scalar (Scalar.fromScalarInt bits))))
    (cached : frame.locals[localId].layout = some layout)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (sized : layout.layout.isSized = true)
    (primitive : Primitive) (range : WrappingRange)
    (repr : layout.layout.backendRepr = .Scalar (.Initialized (value := primitive) (validRange := range)))
    (kind : ValidityVisitor.TypeKind) (name : String)
    (supported : kind = .integer ∨ ∃ b, kind = .boolean ∧ Scalar.fromScalarInt (Prov := Provenance) bits = Scalar.fromBool b)
    (classification : ∀ base : BaseHooks,
      (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).classify
        () layout.ty = pure kind)
    (naming : ∀ base : BaseHooks,
      (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).typeName
        () layout.ty = pure name) :
    ValidityMachine.validateRuntime (PreparedContracts.actualConfig options () remaining span).validity
      () (fuel + 1) (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout) true
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
  obtain ⟨typedCompiler, typedDebug, toOpField, readField, clearField, ghostField,
      classifyField, nameField⟩ := ScalarCopyStage.typed_visitor_primitive_fields_unbound
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts
    PreparedReflection.actual.compiler.lifecycle.calls.runtime base inner.access inner.allocation inner.compiler
    pointers inner.retag options.limits.retag
  have debug : typedCompiler.debugAssertions = false := by rw [typedDebug, fields.debug, debugOff]
  have retain := CanonicalConfigFacts.actual_retain_touched options () remaining span
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent framesBefore frame activeMachine
  have kindQuery : hooks.classify () layout.ty active = .ok kind active := by
    rw [classifyField]
    have query := congrArg (fun f => f active) (classification base)
    simpa only [pure, EStateM.pure] using query
  have nameQuery : hooks.typeName () layout.ty = pure name := by
    rw [nameField]
    exact naming base
  have validator := ScalarCopyStage.validate_primitive_fields_shallow hooks inner.access inner.allocation
    typedCompiler fuel () framesBefore frame machine localId layout bits
    valid live cached sized primitive range repr debug ghostFalse retain name kind
    nameQuery kindQuery supported toOpField readField clearField ghostField
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent framesBefore frame machine) =
      .ok false (Storage.withCurrent framesBefore frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively, Storage.withCurrent, shallow,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  change ValidityMachine.validateRuntime inner.validity () (fuel + 1) _ true _ = _
  rw [hooksEq]
  unfold ValidityMachine.validateRuntime
  simp only [bind, EStateM.bind, recursive]
  exact validator

#print axioms validate_nested_primitive_shallow
open Lean Elab Command in
run_cmd do
  let declaration := ``validate_nested_primitive_shallow
  for dependency in (← collectAxioms declaration) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.RootPrimitiveValidation
