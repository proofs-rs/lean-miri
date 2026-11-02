import duplicate_prefix.CallEntryFacts
import duplicate_prefix.LocalOperands
import duplicate_prefix.RootLocalStages
namespace DuplicatePrefix.CallEntryLocals
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option linter.unusedSimpArgs false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem layout_uncached (compiler : PlaceMachine.CompilerHooks K User Choice) (choice : Choice)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K User) (id : MIR.LocalId) (layout : LocalLayout)
    (valid : id < frame.locals.size) (uncached : frame.locals[id].layout = none)
    (query : compiler.layout choice id (Storage.withCurrent frames frame machine) =
      .ok layout (Storage.withCurrent frames frame machine)) :
    PlaceMachine.layoutLocal compiler choice id (Storage.withCurrent frames frame machine) =
      .ok layout (Storage.withCurrent frames (LocalOperands.cachedLayoutFrame frame id layout valid) machine) := by
  unfold PlaceMachine.layoutLocal
  simp only [Storage.current_frame, bind, EStateM.bind, Frame.getLocal, valid, ↓reduceDIte,
    pure, EStateM.pure, uncached, query]
  simp_all [MachineHooks.currentFrame, MachineHooks.setCurrentFrame, Storage.withCurrent,
    LocalOperands.cachedLayoutFrame, Stack.currentFrame?, Frame.getLocal, Frame.getOrCacheLocalLayout,
    valid, uncached, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, MonadStateOf.set, EStateM.set, pure, EStateM.pure, Except.bind, Except.pure]

theorem root_layout1 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (valid : 1 < frame.locals.size) (uncached : frame.locals[1].layout = none) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localLayout () 1
      (Storage.withCurrent frames frame machine) =
      .ok RootCompilerFacts.sliceLayout
        (Storage.withCurrent frames (LocalOperands.cachedLayoutFrame frame 1 RootCompilerFacts.sliceLayout valid) machine) := by
  apply layout_uncached _ () frames frame machine 1 RootCompilerFacts.sliceLayout valid uncached
  change (PreparedContracts.actualConfig options () remaining span).compiler.layout () 1 _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).layout]
  exact CallEntryFacts.root_compute_local1 frames frame machine body identity callee

theorem root_layout2 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (valid : 2 < frame.locals.size) (uncached : frame.locals[2].layout = none) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localLayout () 2
      (Storage.withCurrent frames frame machine) =
      .ok RootCompilerFacts.usizeLayout
        (Storage.withCurrent frames (LocalOperands.cachedLayoutFrame frame 2 RootCompilerFacts.usizeLayout valid) machine) := by
  apply layout_uncached _ () frames frame machine 2 RootCompilerFacts.usizeLayout valid uncached
  change (PreparedContracts.actualConfig options () remaining span).compiler.layout () 2 _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).layout]
  exact CallEntryFacts.root_compute_local2 frames frame machine body identity callee

theorem destination_cached (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (debug : options.place.debugAssertions = false)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : MIR.LocalId) (layout : LocalLayout) (valid : id < frame.locals.size)
    (cached : frame.locals[id].layout = some layout) (sized : layout.layout.isSized = true) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).evalPlace ()
      ⟨id, #[]⟩ false (Storage.withCurrent frames frame machine) =
      .ok (LocalPlaces.localRuntimePlace frames.size frame id layout).stackView
        (Storage.withCurrent frames frame machine) := by
  let cfg := PreparedContracts.actualConfig options () remaining span
  let projection := ExecutionMachine.projectionHooks (ExecutionMachine.withValidation cfg limits)
  let state := Storage.withCurrent frames frame machine
  have fields := CanonicalConfigFacts.actual_fields options () remaining span
  have getFrame : projection.place.getFrame state = .ok frame state := by
    change cfg.projection.place.getFrame state = .ok frame state
    rw [fields.projectionGetFrame]
    exact Storage.current_frame frames frame machine
  have index : projection.place.frameIndex state = .ok frames.size state := by
    change cfg.projection.place.frameIndex state = .ok frames.size state
    rw [fields.projectionFrameIndex]
    simp [state, Storage.withCurrent, Stack.frameIndex, bind, EStateM.bind,
      get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure, Except.pure, Except.bind]
  have localPlace := LocalPlaces.localToPlace_cached projection.place () frame id frames.size layout state
    valid getFrame index cached sized
  have check := RootLocalStages.place_check_skipped options limits () remaining span debug
    ⟨id, #[]⟩ (LocalPlaces.localRuntimePlace frames.size frame id layout) state
  change projection.place.checkPlaceType () ⟨id, #[]⟩ _ state = _ at check
  have evaluated : PlaceDynamic.evalPlace projection () ⟨id, #[]⟩ false state =
      .ok (LocalPlaces.localRuntimePlace frames.size frame id layout) state := by
    simp [PlaceDynamic.evalPlace, localPlace, check, bind, EStateM.bind, pure, EStateM.pure]
  change ((fun view => pure view.stackView) =<< PlaceDynamic.evalPlace projection () ⟨id, #[]⟩ false) state = _
  simp only [Bind.bindLeft, Bind.bind, EStateM.bind, evaluated, pure, EStateM.pure]
  rfl

theorem storage_live (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : MIR.LocalId) (ty : TyId) (valid : id < frame.locals.size)
    (typed : frame.body.locals[id]? = some ty)
    (trivial : Input.CompilerStorage.veryTriviallySized
      PreparedReflection.actual.compiler.runtime ty = .ok true)
    (dead : frame.locals[id].value = .dead) (noClocks : frame.extra.dataRace = none) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).storageLiveDyn () id .none
      (Storage.withCurrent frames frame machine) = .ok ()
      (Storage.withCurrent frames {frame with locals := (frame.locals.set id
        {value := .live (.immediate .uninit), layout := frame.locals[id].layout} valid)} machine) := by
  apply Storage.storage_live_dead _ frames frame machine id ty valid typed _ dead noClocks
  change (PreparedContracts.actualConfig options () remaining span).lifecycle.storage.veryTriviallySized ty = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).storage]
  exact trivial


theorem root_span0 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localSpan
      RootBody.reflected.body.body 0 (Storage.withCurrent frames frame machine) =
      .ok ⟨601⟩ (Storage.withCurrent frames frame machine) := by
  change (PreparedContracts.actualConfig options () remaining span).compiler.localSpan _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerLocalSpan]
  exact CallEntryFacts.root_local0_span frames frame machine body identity callee

theorem root_span1 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localSpan
      RootBody.reflected.body.body 1 (Storage.withCurrent frames frame machine) =
      .ok ⟨602⟩ (Storage.withCurrent frames frame machine) := by
  change (PreparedContracts.actualConfig options () remaining span).compiler.localSpan _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerLocalSpan]
  exact CallEntryFacts.root_local1_span frames frame machine body identity callee

theorem root_span2 (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (body : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).localSpan
      RootBody.reflected.body.body 2 (Storage.withCurrent frames frame machine) =
      .ok ⟨603⟩ (Storage.withCurrent frames frame machine) := by
  change (PreparedContracts.actualConfig options () remaining span).compiler.localSpan _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).compilerLocalSpan]
  exact CallEntryFacts.root_local2_span frames frame machine body identity callee

theorem set_span (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (location : SpanRef) :
    (do let current ← (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).getFrame
        (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).setFrame
          {current with location := .unwinding location}) (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames {frame with location := .unwinding location} machine) := by
  change (do let current ← MachineHooks.currentFrame
             MachineHooks.setCurrentFrame {current with location := .unwinding location}) _ = _
  simp only [bind, EStateM.bind, Storage.current_frame]
  exact Storage.set_current_frame frames frame {frame with location := .unwinding location} machine


theorem destination_memory (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (place : MPlaceTy Provenance)
    (state : MachineHooks.State MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).placeToOp ()
      (.memory place) state = .ok ⟨.indirect place.mplace, place.layout⟩ state := by
  rfl

theorem get_frame (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).getFrame
      (Storage.withCurrent frames frame machine) = .ok frame (Storage.withCurrent frames frame machine) :=
  Storage.current_frame frames frame machine

theorem set_frame (options : Input.EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (before after : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () remaining span) limits).setFrame after
      (Storage.withCurrent frames before machine) = .ok () (Storage.withCurrent frames after machine) :=
  Storage.set_current_frame frames before after machine

end DuplicatePrefix.CallEntryLocals

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.CallEntryLocals.layout_uncached,
      ``DuplicatePrefix.CallEntryLocals.root_layout1, ``DuplicatePrefix.CallEntryLocals.root_layout2,
      ``DuplicatePrefix.CallEntryLocals.destination_cached, ``DuplicatePrefix.CallEntryLocals.storage_live,
      ``DuplicatePrefix.CallEntryLocals.root_span0, ``DuplicatePrefix.CallEntryLocals.root_span1,
      ``DuplicatePrefix.CallEntryLocals.root_span2, ``DuplicatePrefix.CallEntryLocals.set_span,
      ``DuplicatePrefix.CallEntryLocals.destination_memory,
      ``DuplicatePrefix.CallEntryLocals.get_frame, ``DuplicatePrefix.CallEntryLocals.set_frame] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved entry layout dependency {dependency}"
