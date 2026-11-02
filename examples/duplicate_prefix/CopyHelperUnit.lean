import duplicate_prefix.RootUsizeWrite

namespace DuplicatePrefix.CopyHelperUnit
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

noncomputable def layout : LocalLayout := (PreparedReflection.actual.runtime.lookup 2).toOption.getD CopyCompilerFacts.byteLayout

theorem layout_query : PreparedReflection.actual.runtime.lookup 2 = .ok layout := by decide +kernel

theorem layout_shape : layout.ty = 2 ∧ layout.layout.isSized = true ∧
    layout.layout.fields = .Arbitrary #[] #[] ∧ layout.layout.variants = .Single 0 := by decide +kernel

theorem visit_unit
    (h : ValidityVisitor.Hooks Provenance S C E F A Pad) (c : C) (fuel : Nat)
    (session : ValidityVisitor.Session Provenance) (place : RuntimePlace Provenance) (state : S)
    (kind : h.classify c place.layout.ty state = .ok (.aggregate false false false) state)
    (fields : place.layout.layout.fields = .Arbitrary #[] #[])
    (variants : place.layout.layout.variants = .Single 0)
    (mode : session.ctfeMode = none)
    (inhabited : h.opsemInhabited c place.layout.ty state = .ok true state)
    (debug : h.debugAssertions = false) :
    ValidityVisitor.visit h c (fuel+1) session place state = .ok session state := by
  unfold ValidityVisitor.visit
  unfold_internal ".ValidityVisitor.primitive"
  simp [kind, mode, fields, variants,
    inhabited, debug, bind, EStateM.bind, pure, EStateM.pure]
  cases session
  simp_all

theorem unit_kind : CompilerFactAdapters.validityKind
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts 2 = .ok (.aggregate false false false) := by
  unfold CompilerFactAdapters.validityKind CompilerFacts.boolean
  unfold_fact_helpers
  unfold_validity_query_helpers
  dsimp only
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 2 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 2 :=
    RootMetadataQueries.context_node 2
  simp only [node]
  with_unfolding_all rfl

theorem unit_inhabited : CompilerFacts.boolean
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 2 "opsem_inhabited" = .ok true := by
  unfold CompilerFacts.boolean
  unfold_fact_helpers
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 2 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 2 :=
    RootMetadataQueries.context_node 2
  simp only [node]
  with_unfolding_all rfl

theorem validate_unit_fields_shallow [DecidableEq K]
    (hooks : ValidityVisitor.Hooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra F A ValidityMemory.PaddingHandle)
    (access : ValidityMachine.Access K U)
    (allocation : PlaceMachine.AllocationConfig K (ValidityMachine.UserState U))
    (compiler : ValidityMachine.Compiler K U C)
    (fuel : Nat) (choice : C)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (localId : Miri.MIR.LocalId) (layout : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate .uninit))
    (cached : frame.locals[localId].layout = some layout)
    (sized : layout.layout.isSized = true)
    (fields : layout.layout.fields = .Arbitrary #[] #[])
    (variants : layout.layout.variants = .Single 0)
    (debug : compiler.debugAssertions = false)
    (ghost : machine.user.payload.ghost = false)
    (retain : access.retainTouched = fun machine _ => machine)
    (name : String)
    (nameQuery : hooks.typeName choice layout.ty = pure name)
    (kindQuery : hooks.classify choice layout.ty
      (Storage.withCurrent framesBefore frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) =
      .ok (.aggregate false false false) (Storage.withCurrent framesBefore frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}))
    (inhabited : hooks.opsemInhabited choice layout.ty
      (Storage.withCurrent framesBefore frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}) =
      .ok true (Storage.withCurrent framesBefore frame {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}))
    (hookDebug : hooks.debugAssertions = false)
    (toOpField : hooks.toOp = fun c place => placeToOp
      (ValidityMachine.placeHooks access allocation (ValidityMachine.compilerPolicy compiler)) c place)
    (withGhostField : hooks.withGhostValidation (A := ValidityVisitor.Session Provenance) =
      @ValidityMachine.withGhostValidation K U (ValidityVisitor.Session Provenance)) :
    ValidityVisitor.validatePlace hooks choice (fuel + 1)
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout) false true
      (Storage.withCurrent framesBefore frame machine) = .ok () (Storage.withCurrent framesBefore frame machine) := by
  let place := LocalPlaces.localRuntimePlace framesBefore.size frame localId layout
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent framesBefore frame activeMachine
  let initial : ValidityVisitor.Session Provenance := {
    path := ⟨name, #[]⟩, flags := ⟨true, false⟩, ctfeMode := none, refTracking := none, dataBytes := none }
  have toOp : hooks.toOp choice place active = .ok ⟨.immediate .uninit, layout⟩ active := by
    rw [toOpField]
    exact ScalarCopyStage.place_to_op_ghost access allocation (ValidityMachine.compilerPolicy compiler) choice framesBefore frame
      activeMachine localId layout .uninit valid live cached sized debug rfl
  have visit : ValidityVisitor.visit hooks choice (fuel + 1) initial place active = .ok initial active :=
    visit_unit hooks choice fuel initial place active kindQuery fields variants rfl inhabited hookDebug
  have named : hooks.typeName choice place.layout.ty = pure name := nameQuery
  change ValidityVisitor.validatePlace hooks choice (fuel + 1) place false true _ = _
  unfold ValidityVisitor.validatePlace
  rw [named]
  simp only [bind, EStateM.bind, pure, EStateM.pure, Bool.false_eq_true, ↓reduceIte]
  rw [withGhostField]
  unfold ValidityMachine.withGhostValidation
  simp only [Storage.withCurrent, ghost, Bool.false_eq_true, ↓reduceIte]
  simp only [bind, EStateM.bind]
  erw [toOp]
  simp only [bind, EStateM.bind]
  erw [visit]
  simp only [bind, EStateM.bind]
  unfold_internal ".ValidityVisitor.resetPadding"
  simp only [initial, bind, EStateM.bind, pure, EStateM.pure]
  simp only [active, activeMachine, Storage.withCurrent, ↓reduceIte]
  have restored : {machine.user.payload with ghost := false} = machine.user.payload := by rw [← ghost]
  simp only [restored]


theorem hooks_unit_kind (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).classify
      choice 2 = pure (.aggregate false false false) := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  rw [unit_kind]
  rfl

theorem hooks_unit_name (base : ValidityVisitor.Hooks P S C E F A Pad) (choice : C) :
    (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).typeName
      choice 2 = pure "()" := by
  unfold CompilerFactAdapters.validityHooks
  dsimp only
  unfold_validity_source
  have node : PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 2 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 2 :=
    RootMetadataQueries.context_node 2
  simp only [node]
  with_unfolding_all rfl

theorem validate_unit_shallow
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate .uninit))
    (cached : frame.locals[localId].layout = some layout)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
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
  have typeEq : layout.ty = 2 := by decide +kernel
  let activeMachine := {machine with user := {machine.user with payload := {machine.user.payload with ghost := true}}}
  let active := Storage.withCurrent framesBefore frame activeMachine
  have kindQuery : hooks.classify () layout.ty active = .ok (.aggregate false false false) active := by
    rw [typeEq, classifyField]
    have query := congrArg (fun f => f active) (hooks_unit_kind base ())
    simpa only [pure, EStateM.pure] using query
  have nameQuery : hooks.typeName () layout.ty = pure "()" := by
    rw [typeEq, nameField]
    exact hooks_unit_name base ()
  have inhabited : hooks.opsemInhabited () layout.ty active = .ok true active := by
    rw [typeEq]
    change (CompilerFactAdapters.validityHooks PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts base).opsemInhabited () 2 active = _
    unfold CompilerFactAdapters.validityHooks
    dsimp only
    rw [unit_inhabited]
    rfl
  have hookDebug : hooks.debugAssertions = false := by
    change inner.compiler.debugAssertions = false
    rw [fields.debug, debugOff]
  have validator := validate_unit_fields_shallow hooks inner.access inner.allocation
    typedCompiler fuel () framesBefore frame machine localId layout
    valid live cached layout_shape.2.1 layout_shape.2.2.1 layout_shape.2.2.2 debug ghostFalse retain "()"
    nameQuery kindQuery inhabited hookDebug toOpField ghostField
  have recursive : ValidityMachine.enforceValidityRecursively (Storage.withCurrent framesBefore frame machine) =
      .ok false (Storage.withCurrent framesBefore frame machine) := by
    simp [ValidityMachine.enforceValidityRecursively, Storage.withCurrent, shallow,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  change ValidityMachine.validateRuntime inner.validity () (fuel + 1) _ true _ = _
  rw [hooksEq]
  unfold ValidityMachine.validateRuntime
  simp only [bind, EStateM.bind, recursive]
  exact validator

theorem write_unit_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some layout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeImmediate
      () .uninit
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate .uninit), layout := frame.locals[localId].layout} valid)} machine) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let hooks := (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
  let postFrame := {frame with locals := (frame.locals.set localId
    {value := .live (.immediate .uninit), layout := frame.locals[localId].layout} valid)}
  let postState := Storage.withCurrent framesBefore postFrame machine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have physical := RootUsizeWrite.write_local_no_validate options limits (remaining + 1) span debugOff framesBefore frame machine localId
    old .uninit layout valid live layout_shape.2.1 noClocks ghostFalse
  have enforced : hooks.enforceValidity () layout postState = .ok true postState := by
    change config.projection.place.enforceValidity () layout postState = _
    rw [fields.projectionEnforce]
    simp [ValidityMachine.enforceValidity, postState, Storage.withCurrent, shallow,
      get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure]
  have postValid : localId < postFrame.locals.size := by simpa only [postFrame, Array.size_set] using valid
  have postLive : postFrame.locals[localId].value = .live (.immediate .uninit) := by
    simp [postFrame, valid]
  have postCached : postFrame.locals[localId].layout = some layout := by
    simpa only [postFrame, Array.getElem_set_self] using cached
  have validated : hooks.validate ()
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout) postState = .ok () postState := by
    change config.projection.place.validate () _ postState = _
    rw [fields.projectionValidate, CanonicalConfigFacts.actual_validate_successor, validationFuel]
    exact validate_unit_shallow options remaining span debugOff fuel framesBefore postFrame machine localId
      postValid postLive postCached ghostFalse shallow
  change writePlaceImmediate hooks () .uninit
    (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout) _ = _
  unfold writePlaceImmediate
  simp only [bind, EStateM.bind]
  rw [physical]
  simp only [bind, EStateM.bind]
  erw [enforced]
  exact validated

theorem unit_padding : CompilerCopy.hasPadding PreparedReflection.actual.compiler.runtime false layout = .ok true := by decide +kernel

theorem copy_unit_reduction
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (dest : RuntimePlace Provenance) (destLayout : dest.layout = layout) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).copyOp
      () ⟨.immediate .uninit, layout⟩ dest =
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () remaining span) limits).writeImmediate
      () .uninit dest := by
  let config := PreparedContracts.actualConfig options () remaining span
  let place := (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)).place
  let copy := (ExecutionMachine.withValidation config limits).copy
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have compatible : copy.compatible = CompilerCovariance.compatible PreparedReflection.actual.compiler false := by
    change config.copy.compatible = _
    rw [fields.copyCompatible, debugOff]
  have padding : copy.hasPadding = CompilerCopy.hasPadding PreparedReflection.actual.compiler.runtime false := by
    change config.copy.hasPadding = _
    rw [fields.copyPadding, debugOff]
  have core : copyRuntimePlaceNoValidate place copy () ⟨.immediate .uninit, layout⟩ dest false =
      writePlaceImmediateNoValidate place () .uninit dest := by
    funext state
    unfold copyRuntimePlaceNoValidate
    unfold_internal ".Interpreter.placeLift"
    simp [destLayout, compatible, ScalarCopyStage.same_type_copy, padding, unit_padding,
      layout_shape.2.1, localMemoryLayout, bind, EStateM.bind, pure, EStateM.pure]
  change copyRuntimePlace place copy () ⟨.immediate .uninit, layout⟩ dest false =
    writePlaceImmediate place () .uninit dest
  unfold copyRuntimePlace writePlaceImmediate
  rw [core]
  simp only [destLayout, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]

theorem copy_unit_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel + 1)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : Miri.MIR.LocalId) (old : Immediate Provenance)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some layout)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).copyOp
      () ⟨.immediate .uninit,layout⟩
      (LocalPlaces.localRuntimePlace framesBefore.size frame localId layout)
      (Storage.withCurrent framesBefore frame machine) =
      .ok () (Storage.withCurrent framesBefore {frame with locals := (frame.locals.set localId
        {value := .live (.immediate .uninit), layout := frame.locals[localId].layout} valid)} machine) := by
  rw [copy_unit_reduction options limits (remaining+1) span debugOff _ rfl]
  exact write_unit_shallow options limits remaining span debugOff fuel validationFuel framesBefore frame machine
    localId old valid live cached noClocks ghostFalse shallow

#print axioms write_unit_shallow
open Lean Elab Command in
run_cmd do
  for declaration in [``visit_unit, ``validate_unit_fields_shallow, ``validate_unit_shallow, ``write_unit_shallow, ``copy_unit_reduction, ``copy_unit_shallow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.CopyHelperUnit
