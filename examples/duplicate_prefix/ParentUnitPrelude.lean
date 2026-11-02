import Miri.Interpreter.Aggregate
import duplicate_prefix.CopyHelperUnit
import duplicate_prefix.RootMetadataQueries
import duplicate_prefix.AllocationCopy
import duplicate_prefix.LayoutLookupProof
import duplicate_prefix.ActualLocalPlace
import duplicate_prefix.SourceSteps
import duplicate_prefix.GuardCompilerFacts
import duplicate_prefix.CopyRuntimeCallFacts
import duplicate_prefix.CallLocalRead
import duplicate_prefix.BoundUnitValidation

/-! Exact empty-tuple branch of the production Aggregate.writeAggregate routine.
The callback premises are the three real suboperations used by that routine;
this lemma does not replace the aggregate dispatcher with a simplified model. -/
namespace DuplicatePrefix.ParentUnitPrelude
open Miri Miri.ABI Miri.Input Miri.Memory Miri.Interpreter
open RootMetadataQueries
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000

private def checkedOk {Error Value : Type} :
    (value : Except Error Value) → value.isOk = true → Value
  | .ok value, _ => value
  | .error _, impossible => False.elim (by cases impossible)

private theorem checkedOk_eq {Error Value : Type}
    (value : Except Error Value) (success : value.isOk = true) :
    value = .ok (checkedOk value success) := by
  cases value with
  | ok value => rfl
  | error error => cases success

noncomputable def unitNodeQuery :=
  PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 2
theorem contextNodeEq :
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 2 =
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.toRuntimeMetadata.node 2 := by
  change RootMetadataQueries.context.runtime.node 2 = RootMetadataQueries.context.runtime.toRuntimeMetadata.node 2
  exact RootMetadataQueries.context_node 2
theorem unit_node_supported : unitNodeQuery.isOk = true := by
  change (PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 2).isOk = true
  rw [contextNodeEq]
  decide +kernel
noncomputable def unitNode := checkedOk unitNodeQuery unit_node_supported

theorem context_unit_node :
    PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context.runtime.node 2 = .ok unitNode := by
  exact checkedOk_eq _ _

theorem unit_discriminant_type :
    CompilerFacts.requiredType PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context
      2 "discriminant_type" = .ok 1 := by
  change CompilerFacts.requiredType context 2 "discriminant_type" = .ok 1
  unfold CompilerFacts.requiredType CompilerFacts.optionalType
  unfold_fact_helpers
  simp only [context_node]
  with_unfolding_all rfl

theorem unit_discriminant_layout :
    CompilerDiscriminantFacts.discriminantLayout
      PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context 2 = .ok CopyCompilerFacts.byteLayout := by
  unfold CompilerDiscriminantFacts.discriminantLayout
  rw [unit_discriminant_type]
  exact CopyCompilerFacts.compiler_byte_layout

theorem actual_unit_discriminant_layout
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.discriminantHooks
      (PreparedContracts.actualConfig options () (remaining + 1) span)).discriminantLayout
        () 2 state = .ok CopyCompilerFacts.byteLayout state := by
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  unfold ExecutionMachine.discriminantHooks
  rw [fields.discriminant]
  unfold CompilerScalarLeaves.discriminant
  simp [CompilerDiscriminantFacts.hooks, unit_discriminant_layout,
    bind, EStateM.bind, pure, EStateM.pure]
  unfold_internal ".CompilerScalarLeaves.lift"
  rfl

theorem actual_unit_enforce_shallow
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (shallow : machine.user.payload.validation = .Shallow) :
    (PreparedContracts.actualConfig options () (remaining + 1) span).compiler.enforceValidity
      () CopyHelperUnit.layout (Storage.withCurrent frames frame machine) =
      .ok true (Storage.withCurrent frames frame machine) := by
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  rw [fields.compilerEnforce]
  simp [ValidityMachine.enforceValidity, shallow, bind, EStateM.bind,
    get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure,
    Storage.withCurrent]

theorem actual_unit_to_op_cached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : (2 : LocalId) < frame.locals.size)
    (live : frame.locals[2].value = .live (.immediate .uninit))
    (cached : frame.locals[2].layout = some CopyHelperUnit.layout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    (ExecutionMachine.discriminantHooks
      (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () (remaining + 1) span) limits)).toOp ()
      (LocalPlaces.localRuntimePlace frames.size frame 2 CopyHelperUnit.layout)
      (Storage.withCurrent frames frame machine) =
      .ok ⟨.immediate .uninit, CopyHelperUnit.layout⟩ (Storage.withCurrent frames frame machine) := by
  change (ExecutionMachine.callHooks
      (PreparedContracts.actualConfig options () (remaining + 1) span) limits).placeToOp ()
      (LocalPlaces.localRuntimePlace frames.size frame 2 CopyHelperUnit.layout).stackView
      (Storage.withCurrent frames frame machine) = _
  exact CallLocalRead.place_to_op_cached options limits (remaining + 1) span debugOff
    frames frame machine 2 CopyHelperUnit.layout .uninit valid live cached
    CopyHelperUnit.layout_shape.2.1 noClocks ghost

/-- The production discriminant writer is a no-op for a zero-valued
single-variant layout once its real layout lookup and operand conversion
succeed. This isolates the source tag_for_variant/read_discriminant branch. -/
theorem write_discriminant_single_zero [PointerProvenance P]
    (hooks : DiscriminantHooks P S C V) (choice : C) (dest : V)
    (state : S) (discrLayout opLayout : TyAndLayout MIR.TyId)
    (destSingle : (hooks.destLayout dest).layout.variants = .Single 0)
    (destInhabited : (hooks.destLayout dest).layout.uninhabited = false)
    (discrLookup : hooks.discriminantLayout choice (hooks.destLayout dest).ty state = .ok discrLayout state)
    (toOp : hooks.toOp choice dest state = .ok ⟨.immediate .uninit, opLayout⟩ state)
    (opTy : opLayout.ty = (hooks.destLayout dest).ty)
    (opSingle : opLayout.layout.variants = .Single 0)
    (opInhabited : opLayout.layout.uninhabited = false) :
    Discriminant.writeDiscriminant hooks choice 0 dest state = .ok () state := by
  have tag : Discriminant.tagForVariant hooks choice (hooks.destLayout dest) 0 state = .ok none state := by
    unfold_internal ".Discriminant.tagForVariant"
    simp [LayoutData.isVariantUninhabited, destSingle, destInhabited]
    rfl
  have op : hooks.toOp choice dest state = .ok ⟨.immediate .uninit, opLayout⟩ state := toOp
  have read : Discriminant.readDiscriminant hooks choice ⟨.immediate .uninit, opLayout⟩ state = .ok 0 state := by
    unfold Discriminant.readDiscriminant
    rw [show (⟨.immediate .uninit, opLayout⟩ : OpTy P).layout.ty = opLayout.ty from rfl]
    simp only [bind, EStateM.bind]
    rw [opTy, discrLookup]
    simp [opSingle, opInhabited, LayoutData.isUninhabited]
    rfl
  simp only [Discriminant.writeDiscriminant, tag, bind, EStateM.bind,
    pure, EStateM.pure, op, read]
  rfl


theorem actual_write_unit_discriminant
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : (2 : LocalId) < frame.locals.size)
    (live : frame.locals[2].value = .live (.immediate .uninit))
    (cached : frame.locals[2].layout = some CopyHelperUnit.layout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) :
    Discriminant.writeDiscriminant
      (ExecutionMachine.discriminantHooks
        (ExecutionMachine.withValidation
          (PreparedContracts.actualConfig options () (remaining + 1) span) limits))
      () 0 (LocalPlaces.localRuntimePlace frames.size frame 2 CopyHelperUnit.layout)
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
  let place := LocalPlaces.localRuntimePlace frames.size frame 2 CopyHelperUnit.layout
  let state := Storage.withCurrent frames frame machine
  have destSingle : ((ExecutionMachine.discriminantHooks
      (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () (remaining + 1) span) limits)).destLayout place).layout.variants = .Single 0 := by
    rfl
  have destInhabited : ((ExecutionMachine.discriminantHooks
      (ExecutionMachine.withValidation
        (PreparedContracts.actualConfig options () (remaining + 1) span) limits)).destLayout place).layout.uninhabited = false := by
    change CopyHelperUnit.layout.layout.uninhabited = false
    decide +kernel
  have lookup := actual_unit_discriminant_layout options remaining span state
  have operand := actual_unit_to_op_cached options limits remaining span debugOff frames frame machine
    valid live cached noClocks ghost
  have opTy : CopyHelperUnit.layout.ty = place.layout.ty := by rfl
  have opSingle : CopyHelperUnit.layout.layout.variants = .Single 0 := CopyHelperUnit.layout_shape.2.2.2
  have opInhabited : CopyHelperUnit.layout.layout.uninhabited = false := by decide +kernel
  exact write_discriminant_single_zero _ () place state CopyCompilerFacts.byteLayout CopyHelperUnit.layout
    destSingle destInhabited lookup operand opTy opSingle opInhabited

theorem actual_unit_validate_shallow
    (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate .uninit))
    (cached : frame.locals[localId].layout = some CopyHelperUnit.layout)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (budget : options.limits.validation = fuel + 1) :
    (PreparedContracts.actualConfig options () (remaining + 1) span).compiler.validate
      () (LocalPlaces.localRuntimePlace frames.size frame localId CopyHelperUnit.layout)
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
  rw [CanonicalConfigFacts.actual_validate_successor options () remaining span, budget]
  exact CopyHelperUnit.validate_unit_shallow options remaining span debugOff fuel frames frame
    machine localId valid live cached ghost shallow

/-- The actual outer `withValidation` callback at the aggregate boundary. This
uses the bound typed visitor, including the real retag binding and shallow
primitive validator, rather than the pre-binding config callback. -/
theorem actual_unit_bound_validate_shallow
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : limits.validation = fuel + 1)
    (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : LocalId) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate .uninit))
    (cached : frame.locals[localId].layout = some CopyHelperUnit.layout)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.withValidation
      (PreparedContracts.actualConfig options () (remaining + 1) span) limits).compiler.validate
      () (LocalPlaces.localRuntimePlace frames.size frame localId CopyHelperUnit.layout)
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
  exact BoundUnitValidation.compiler_validate options limits (remaining + 1) span debugOff fuel
    validationFuel frames frame machine localId valid live cached ghost shallow

theorem language_local2_normalized (frame : CompilerFrameContext.ActualFrame)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance) :
    CompilerFrameContext.normalizedLocalType PreparedReflection.actual.compiler frame 2 = .ok 2 := by
  unfold CompilerFrameContext.normalizedLocalType CompilerFrameContext.normalizedBody CompilerFrameContext.bodyOfFrame
  rw [body, identity, callee]
  with_unfolding_all rfl

theorem language_compute_local2
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance) :
    CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler 2
      (Storage.withCurrent framesBefore frame machine) =
      .ok CopyHelperUnit.layout (Storage.withCurrent framesBefore frame machine) := by
  have normalized := language_local2_normalized frame body identity callee
  unfold CompilerFrameContext.computeLocalLayout
  simp only [MachineHooks.currentFrame, Storage.withCurrent, Stack.currentFrame?, Array.back?_push,
    bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  rw [normalized]
  with_unfolding_all change (match PreparedReflection.actual.runtime.lookup 2 with
    | .ok value => EStateM.Result.ok value (Storage.withCurrent framesBefore frame machine)
    | .error error => EStateM.Result.error (StepError.unsupported s!"compiler frame query: {toString error}")
        (Storage.withCurrent framesBefore frame machine)) = _
  rw [CopyHelperUnit.layout_query]
  rfl

theorem parent_live1_statement :
    ∃ block statement,
      CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]? = some block ∧
      block.statements[0]? = some statement ∧ statement.kind = .StorageLive 1 := by
  let block := CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]'(by decide)
  let statement := block.statements[0]'(by decide)
  refine ⟨block, statement, ?_, ?_, ?_⟩
  · change CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]? = some _
    simp [block]
  · change block.statements[0]? = some _
    simp [statement]
  · change statement.kind = _
    with_unfolding_all rfl

theorem parent_live2_statement :
    ∃ block statement,
      CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]? = some block ∧
      block.statements[1]? = some statement ∧ statement.kind = .StorageLive 2 := by
  let block := CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]'(by decide)
  let statement := block.statements[1]'(by decide)
  refine ⟨block, statement, ?_, ?_, ?_⟩
  · change CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]? = some _
    simp [block]
  · change block.statements[1]? = some _
    simp [statement]
  · change statement.kind = _
    with_unfolding_all rfl

theorem parent_unit_statement :
    ∃ block statement,
      CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]? = some block ∧
      block.statements[2]? = some statement ∧
      statement.kind = .Assign ⟨2,#[]⟩ (.Aggregate .Tuple #[]) := by
  let block := CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]'(by decide)
  let statement := block.statements[2]'(by decide)
  refine ⟨block, statement, ?_, ?_, ?_⟩
  · change CopyPreconditions.Bodies.checkLanguage.loaded.body.basicBlocks[0]? = some _
    simp [block]
  · change block.statements[2]? = some _
    simp [statement]
  · change statement.kind = _
    with_unfolding_all rfl

theorem parent_storage_live_two
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (framesBefore : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid1 : (1 : LocalId) < frame.locals.size) (valid2 : (2 : LocalId) < frame.locals.size)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (dead1 : frame.locals[1].value = .dead) (dead2 : frame.locals[2].value = .dead)
    (noClocks : frame.extra.dataRace = none) :
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore (SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1) machine, .ok true) ∧
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore (SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1) machine) =
      (Storage.withCurrent framesBefore
        (SourceSteps.liveFrame (SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1) ⟨0,1⟩ 2
          (by simpa [SourceSteps.liveFrame, Array.size_set] using valid2)) machine, .ok true) := by
  obtain ⟨block0, statement0, blockAt0, statementAt0, kind0⟩ := parent_live1_statement
  obtain ⟨block1, statement1, blockAt1, statementAt1, kind1⟩ := parent_live2_statement
  have blockAt0' : frame.body.basicBlocks[0]? = some block0 := by rw [body]; exact blockAt0
  have blockAt1' : frame.body.basicBlocks[0]? = some block1 := by rw [body]; exact blockAt1
  have statementAt0' : block0.statements[0]? = some statement0 := statementAt0
  have statementAt1' : block1.statements[1]? = some statement1 := statementAt1
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have trivial : (PreparedContracts.actualConfig options () (remaining+1) span).lifecycle.storage.veryTriviallySized 0 = .ok true := by
    rw [fields.storage]
    exact RootCompilerFacts.root_storage_trivial_bool
  have trivialUnit : (PreparedContracts.actualConfig options () (remaining+1) span).lifecycle.storage.veryTriviallySized 2 = .ok true := by
    rw [fields.storage]
    exact RootCompilerFacts.root_storage_trivial_type2
  constructor
  · apply SourceSteps.storage_live_exact
      (config := PreparedContracts.actualConfig options () (remaining+1) span) (limits := limits)
      (choice := ()) (framesBefore := framesBefore) (frame := frame) (machine := machine)
      (location := ⟨0,0⟩) (block := block0) (statement := statement0) (localId := 1) (ty := 0)
    · exact location
    · exact blockAt0'
    · exact statementAt0'
    · exact kind0
    · have types := GuardCompilerFacts.source_body_shapes.2.1
      rw [body, types]
      decide
    · exact trivial
    · exact dead1
    · exact noClocks
  · have frame1Valid2 : (2 : LocalId) < (SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1).locals.size := by
      simpa [SourceSteps.liveFrame, Array.size_set] using valid2
    have frame1Dead2 : (SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1).locals[2].value = .dead := by
      simp [SourceSteps.liveFrame, Array.getElem_set, dead2,
        show (2 : LocalId) ≠ 1 by decide]
    have frame1NoClocks : (SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1).extra.dataRace = none := by
      exact noClocks
    apply SourceSteps.storage_live_exact
      (config := PreparedContracts.actualConfig options () (remaining+1) span) (limits := limits)
      (choice := ()) (framesBefore := framesBefore)
      (frame := SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1) (machine := machine)
      (location := ⟨0,1⟩) (block := block1) (statement := statement1) (localId := 2) (ty := 2)
    · simpa [SourceSteps.liveFrame] using location
    · exact blockAt1'
    · exact statementAt1'
    · exact kind1
    · have types := GuardCompilerFacts.source_body_shapes.2.1
      simp only [SourceSteps.liveFrame]
      rw [body, types]
      rfl
    · exact trivialUnit
    · exact frame1Dead2
    · exact frame1NoClocks

theorem write_empty_tuple
    (hooks : AggregateHooks P S C V) (choice : C) (dest : V) (before after : S)
    (writeDiscriminant : hooks.writeDiscriminant choice 0 dest before = .ok () before)
    (enforce : hooks.enforceValidity choice (hooks.placeLayout dest) before = .ok true before)
    (validate : hooks.validate choice dest before = .ok () after) :
    writeAggregate hooks choice .Tuple #[] dest before = .ok () after := by
  simp [writeAggregate, writeDiscriminant, enforce, validate, bind, EStateM.bind,
    pure, EStateM.pure, ← Array.forIn_toList]


theorem actual_write_empty_tuple
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : limits.validation = fuel + 1)
    (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : (2 : LocalId) < frame.locals.size)
    (live : frame.locals[2].value = .live (.immediate .uninit))
    (cached : frame.locals[2].layout = some CopyHelperUnit.layout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ((ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits).writeAggregate)
      () .Tuple #[]
      (LocalPlaces.localRuntimePlace frames.size frame 2 CopyHelperUnit.layout)
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
  unfold ExecutionMachine.rvalueHooks
  apply write_empty_tuple
  · exact actual_write_unit_discriminant options limits remaining span debugOff frames frame
      machine valid live cached noClocks ghost
  · exact actual_unit_enforce_shallow options remaining span frames frame machine shallow
  · exact actual_unit_bound_validate_shallow options limits remaining span debugOff fuel
      validationFuel frames frame machine 2 valid live cached ghost shallow

theorem actual_parent_tuple_rvalue
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : limits.validation = fuel + 1)
    (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid : (2 : LocalId) < frame.locals.size)
    (live : frame.locals[2].value = .live (.immediate .uninit))
    (cached : frame.locals[2].layout = some CopyHelperUnit.layout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits)
      () (.Aggregate .Tuple #[]) ⟨2, #[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let state := Storage.withCurrent frames frame machine
  let place := LocalPlaces.localRuntimePlace frames.size frame 2 CopyHelperUnit.layout
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation config limits)
  let hooks := projection.place
  have fields := CanonicalConfigFacts.actual_fields options () (remaining + 1) span
  have getFrame : hooks.getFrame state = .ok frame state := by
    change config.projection.place.getFrame state = .ok frame state
    rw [fields.projectionGetFrame]
    exact Storage.current_frame frames frame machine
  have frameIndex : hooks.frameIndex state = .ok frames.size state := by
    change config.projection.place.frameIndex state = .ok frames.size state
    rw [fields.projectionFrameIndex]
    simp [state, Storage.withCurrent, Stack.frameIndex, Array.isEmpty_push,
      bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
      pure, EStateM.pure, Except.pure, Except.bind]
  have localPlace := LocalPlaces.localToPlace_cached hooks () frame 2 frames.size
    CopyHelperUnit.layout state valid getFrame frameIndex cached CopyHelperUnit.layout_shape.2.1
  have check := RootLocalStages.place_check_skipped options limits () (remaining + 1) span
    debugOff ⟨2, #[]⟩ place state
  have evalPlace := LocalPlaces.evalPlace_local_empty projection () 2 frame frames.size
    CopyHelperUnit.layout state localPlace check
  have evalPlaceRvalue : (ExecutionMachine.rvalueHooks config limits).evalPlace
      () ⟨2, #[]⟩ true state = .ok place state := by
    change PlaceDynamic.evalPlace projection () ⟨2, #[]⟩ true state = _
    exact evalPlace
  change evalRvalueIntoPlace
    (ExecutionMachine.rvalueHooks config limits) () (.Aggregate .Tuple #[]) ⟨2, #[]⟩ state = _
  simp only [evalRvalueIntoPlace, evalPlace, bind, EStateM.bind, pure, EStateM.pure]
  rw [evalPlaceRvalue]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  exact actual_write_empty_tuple options limits remaining span debugOff fuel validationFuel
    frames frame machine valid live cached noClocks ghost shallow

theorem actual_parent_tuple_rvalue_uncached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : limits.validation = fuel + 1)
    (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (valid : (2 : LocalId) < frame.locals.size)
    (live : frame.locals[2].value = .live (.immediate .uninit))
    (uncached : frame.locals[2].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining + 1) span) limits)
      () (.Aggregate .Tuple #[]) ⟨2, #[]⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        (LocalPlaces.cachePlaceLayout frame 2 CopyHelperUnit.layout valid) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining + 1) span
  let state := Storage.withCurrent frames frame machine
  let updatedFrame := LocalPlaces.cachePlaceLayout frame 2 CopyHelperUnit.layout valid
  let updated := Storage.withCurrent frames updatedFrame machine
  have layoutQuery := language_compute_local2 frames frame machine body identity callee
  have placeEval : (ExecutionMachine.rvalueHooks config limits).evalPlace () ⟨2, #[]⟩ true state =
      .ok (LocalPlaces.localRuntimePlace frames.size updatedFrame 2 CopyHelperUnit.layout) updated := by
    exact ActualLocalPlace.uncached options limits (remaining + 1) span debugOff frames frame machine
      2 CopyHelperUnit.layout valid uncached CopyHelperUnit.layout_shape.2.1 layoutQuery
  have validUpdated : (2 : LocalId) < updatedFrame.locals.size := by
    simpa [updatedFrame, LocalPlaces.cachePlaceLayout, Array.size_set] using valid
  have cached : updatedFrame.locals[2].layout = some CopyHelperUnit.layout := by
    simp [updatedFrame, LocalPlaces.cachePlaceLayout, valid]
  have liveUpdated : updatedFrame.locals[2].value = .live (.immediate .uninit) := by
    simp [updatedFrame, LocalPlaces.cachePlaceLayout, live, valid]
  have aggregate := actual_write_empty_tuple options limits remaining span
    debugOff fuel validationFuel frames updatedFrame machine validUpdated liveUpdated cached noClocks ghost shallow
  change evalRvalueIntoPlace (ExecutionMachine.rvalueHooks config limits)
    () (.Aggregate .Tuple #[]) ⟨2, #[]⟩ state = _
  simp only [evalRvalueIntoPlace, bind, EStateM.bind, pure, EStateM.pure]
  rw [placeEval]
  exact aggregate

private def parentAfterLiveTwo (frame : CompilerFrameContext.ActualFrame)
    (valid1 : (1 : LocalId) < frame.locals.size)
    (valid2 : (2 : LocalId) < frame.locals.size) :=
  let frame1 := SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1
  SourceSteps.liveFrame frame1 ⟨0,1⟩ 2
    (by simpa [frame1, SourceSteps.liveFrame, Array.size_set] using valid2)

theorem actual_parent_three_statement_steps
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : limits.validation = fuel + 1)
    (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid1 : (1 : LocalId) < frame.locals.size)
    (valid2 : (2 : LocalId) < frame.locals.size)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (dead1 : frame.locals[1].value = .dead)
    (dead2 : frame.locals[2].value = .dead)
    (uncached2 : frame.locals[2].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ∃ afterFrame : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (Storage.withCurrent frames frame machine) =
        (Storage.withCurrent frames (SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1) machine, .ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (Storage.withCurrent frames (SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1) machine) =
        (Storage.withCurrent frames (parentAfterLiveTwo frame valid1 valid2) machine, .ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (Storage.withCurrent frames (parentAfterLiveTwo frame valid1 valid2) machine) =
        (Storage.withCurrent frames {afterFrame with location := .mir ⟨0,2+1⟩} machine, .ok true) := by
  have lives := parent_storage_live_two options limits remaining span frames frame machine
    valid1 valid2 body identity callee location dead1 dead2 noClocks
  let frame1 := SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1
  have valid2After : (2 : LocalId) < frame1.locals.size := by
    simpa [frame1, SourceSteps.liveFrame, Array.size_set] using valid2
  let frame2 := parentAfterLiveTwo frame valid1 valid2
  have frame2Valid2 : (2 : LocalId) < frame2.locals.size := by
    simpa [frame2, parentAfterLiveTwo, SourceSteps.liveFrame, Array.size_set] using valid2
  have frame2Body : frame2.body = CopyPreconditions.Bodies.checkLanguage.loaded.body := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame, body]
  have frame2Identity : frame2.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame, identity]
  have frame2Callee : frame2.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame, callee]
  have frame2Location : frame2.location = .mir ⟨0,2⟩ := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame]
  have frame2Live : frame2.locals[2].value = .live (.immediate .uninit) := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame, Array.getElem_set, dead2,
      show (2 : LocalId) ≠ 1 by decide]
  have frame2Uncached : frame2.locals[2].layout = none := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame, Array.getElem_set, uncached2,
      show (2 : LocalId) ≠ 1 by decide]
  have frame2NoClocks : frame2.extra.dataRace = none := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame, noClocks]
  obtain ⟨block, statement, blockAt, statementAt, kind⟩ := parent_unit_statement
  have blockAt' : frame2.body.basicBlocks[0]? = some block := by rw [frame2Body]; exact blockAt
  have statementAt' : block.statements[2]? = some statement := statementAt
  have effect := actual_parent_tuple_rvalue_uncached options limits remaining span debugOff fuel
    validationFuel frames frame2 machine frame2Body frame2Identity frame2Callee frame2Valid2
    frame2Live frame2Uncached frame2NoClocks ghost shallow
  let frame3 := LocalPlaces.cachePlaceLayout frame2 2 CopyHelperUnit.layout frame2Valid2
  have frame3Location : frame3.location = .mir ⟨0,2⟩ := by
    simp [frame3, LocalPlaces.cachePlaceLayout, frame2Location]
  have step := SourceSteps.assign_exact
    (config := PreparedContracts.actualConfig options () (remaining+1) span) (limits := limits)
    (choice := ()) (framesBefore := frames) (frame := frame2) (afterFrame := frame3)
    (machine := machine) (afterMachine := machine) (location := ⟨0,2⟩)
    (block := block) (statement := statement) (place := ⟨2,#[]⟩)
    (value := .Aggregate .Tuple #[])
  have stepResult := step frame2Location blockAt' statementAt' kind effect frame3Location
  refine ⟨frame3, lives.1, lives.2, ?_⟩
  simpa only [Nat.reduceAdd] using stepResult

noncomputable def afterPrelude (frame : CompilerFrameContext.ActualFrame)
    (valid1 : (1 : Miri.MIR.LocalId) < frame.locals.size)
    (valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size) :=
  let first := SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1
  let second := SourceSteps.liveFrame first ⟨0,1⟩ 2 (by simpa [first,SourceSteps.liveFrame] using valid2)
  let third := LocalPlaces.cachePlaceLayout second 2 CopyHelperUnit.layout
    (by simpa [second,first,SourceSteps.liveFrame] using valid2)
  {third with location := .mir ⟨0,3⟩}

theorem actual_parent_three_statement_steps_exact
    [DecidableEq MiriMemoryKind]
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : limits.validation = fuel + 1)
    (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (valid1 : (1 : LocalId) < frame.locals.size)
    (valid2 : (2 : LocalId) < frame.locals.size)
    (body : frame.body = CopyPreconditions.Bodies.checkLanguage.loaded.body)
    (identity : frame.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity)
    (callee : frame.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (dead1 : frame.locals[1].value = .dead)
    (dead2 : frame.locals[2].value = .dead)
    (uncached2 : frame.locals[2].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    ∃ afterFrame : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (Storage.withCurrent frames frame machine) =
        (Storage.withCurrent frames (SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1) machine, .ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (Storage.withCurrent frames (SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1) machine) =
        (Storage.withCurrent frames (parentAfterLiveTwo frame valid1 valid2) machine, .ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
        (Storage.withCurrent frames (parentAfterLiveTwo frame valid1 valid2) machine) =
        (Storage.withCurrent frames {afterFrame with location := .mir ⟨0,2+1⟩} machine, .ok true) ∧
      {afterFrame with location := .mir ⟨0,3⟩} = afterPrelude frame valid1 valid2 := by
  have lives := parent_storage_live_two options limits remaining span frames frame machine
    valid1 valid2 body identity callee location dead1 dead2 noClocks
  let frame1 := SourceSteps.liveFrame frame ⟨0,0⟩ 1 valid1
  have valid2After : (2 : LocalId) < frame1.locals.size := by
    simpa [frame1, SourceSteps.liveFrame, Array.size_set] using valid2
  let frame2 := parentAfterLiveTwo frame valid1 valid2
  have frame2Valid2 : (2 : LocalId) < frame2.locals.size := by
    simpa [frame2, parentAfterLiveTwo, SourceSteps.liveFrame, Array.size_set] using valid2
  have frame2Body : frame2.body = CopyPreconditions.Bodies.checkLanguage.loaded.body := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame, body]
  have frame2Identity : frame2.bodyIdentity = CopyPreconditions.Bodies.checkLanguage.loaded.identity := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame, identity]
  have frame2Callee : frame2.functionInstance = CopyPreconditions.Bodies.checkLanguage.fnInstance := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame, callee]
  have frame2Location : frame2.location = .mir ⟨0,2⟩ := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame]
  have frame2Live : frame2.locals[2].value = .live (.immediate .uninit) := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame, Array.getElem_set, dead2,
      show (2 : LocalId) ≠ 1 by decide]
  have frame2Uncached : frame2.locals[2].layout = none := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame, Array.getElem_set, uncached2,
      show (2 : LocalId) ≠ 1 by decide]
  have frame2NoClocks : frame2.extra.dataRace = none := by
    simp [frame2, parentAfterLiveTwo, frame1, SourceSteps.liveFrame, noClocks]
  obtain ⟨block, statement, blockAt, statementAt, kind⟩ := parent_unit_statement
  have blockAt' : frame2.body.basicBlocks[0]? = some block := by rw [frame2Body]; exact blockAt
  have statementAt' : block.statements[2]? = some statement := statementAt
  have effect := actual_parent_tuple_rvalue_uncached options limits remaining span debugOff fuel
    validationFuel frames frame2 machine frame2Body frame2Identity frame2Callee frame2Valid2
    frame2Live frame2Uncached frame2NoClocks ghost shallow
  let frame3 := LocalPlaces.cachePlaceLayout frame2 2 CopyHelperUnit.layout frame2Valid2
  have frame3Location : frame3.location = .mir ⟨0,2⟩ := by
    simp [frame3, LocalPlaces.cachePlaceLayout, frame2Location]
  have step := SourceSteps.assign_exact
    (config := PreparedContracts.actualConfig options () (remaining+1) span) (limits := limits)
    (choice := ()) (framesBefore := frames) (frame := frame2) (afterFrame := frame3)
    (machine := machine) (afterMachine := machine) (location := ⟨0,2⟩)
    (block := block) (statement := statement) (place := ⟨2,#[]⟩)
    (value := .Aggregate .Tuple #[])
  have stepResult := step frame2Location blockAt' statementAt' kind effect frame3Location
  refine ⟨frame3, lives.1, lives.2, ?_, rfl⟩
  simpa only [Nat.reduceAdd] using stepResult

#print axioms actual_parent_three_statement_steps_exact

end DuplicatePrefix.ParentUnitPrelude

#print axioms DuplicatePrefix.ParentUnitPrelude.write_empty_tuple
#print axioms DuplicatePrefix.ParentUnitPrelude.actual_write_empty_tuple
#print axioms DuplicatePrefix.ParentUnitPrelude.actual_parent_tuple_rvalue
#print axioms DuplicatePrefix.ParentUnitPrelude.actual_parent_tuple_rvalue_uncached
#print axioms DuplicatePrefix.ParentUnitPrelude.actual_parent_three_statement_steps
