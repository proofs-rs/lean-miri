import empty_function.ReturnMemory
import empty_function.FrameExit
import empty_function.ReturnContinuation

/-! Actual Return for the unit frame with an empty owned-protector list. -/
namespace EmptyFunction.ReturnStep
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Return observations follow from the checked source meaning, independently
of the compiler's choice of syntax IDs. -/
theorem block_observations (s : Static) (metadata : Metadata s) :
    metadata.entry.block.cleanup = false ∧ metadata.entry.block.statements.size = 1 ∧
      ∃ term : TerminatorNode,
        s.loaded.tables.terminators.lookup metadata.entry.block.terminator.index = .ok term ∧
          term.kind = .Return := by
  exact Meaning.entry_return s.loaded.tables s.loaded.body Program.contents metadata.entry
    metadata.body metadata.entry_references Program.contents_cleanup
    Program.contents_statement_count Program.contents_return

def control (s : Static) : ControlHooks Provenance LocalLayout MachineHooks.FrameExtra
    (MachineHooks.MachineState MiriMemoryKind RootUser) Unit (OpTy Provenance) :=
  let h := ExecutionMachine.withValidation s.cfg s.limits
  let calls := ExecutionMachine.callHooks h s.limits
  let helpers := ExecutionCalls.helpers h.helpers calls
  ExecutionControl.hooks h.control.bodySpan h.lifecycle h.access
    (ExecutionMachine.projectionHooks h).place h.copy h.retag helpers h.unwindTerminateFunction

 theorem source (s : Static) :
    (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame =
      ControlFlow.returnFromCurrentFrame (control s) := rfl

 theorem read (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (locals : frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}])
    (noClocks : frame.extra.dataRace = none) :
    (control s).returnOperand () (BodyStep.current frames frame machine) =
      (BodyStep.current frames frame machine,.ok ⟨.immediate .uninit,s.abi.ret.layout⟩) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have place := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    leaves (remaining+1) metadata.construction s.cfg outer
  have dictionaries := CanonicalDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    leaves (remaining+1) metadata.construction s.cfg outer
  change MachineHooks.run (s.cfg.projection.place.localToOp () 0) _ = _
  rw [place.projection]
  unfold MachineHooks.run Call.run
  cases flag : machine.user.payload.ghost <;> with_unfolding_all
    simp [ValidityMachine.placeHooks,ValidityMachine.compilerPolicy,PlaceMachine.placeHooks,
      PlaceMachine.localToOp,PlaceMachine.localToOpCore,PlaceMachine.layoutLocal,
      ValidityMachine.validationInProgress,metadata.unitSized,dictionaries.debug.trans profile.debug,
      noClocks,flag,MachineHooks.afterLocalRead,MachineHooks.currentFrame,
      BodyStep.current,LocalUnit.current,locals,Frame.getLocalOperand,Frame.getLocal,Stack.currentFrame?,
      LocalState.access,Except.mapError,Except.pure,Except.bind,
      get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

 theorem pop (s : Static) (frames : Array BodyStep.F) (frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (tracker : MachineHooks.BorrowState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some {})
    (thread : Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    (control s).popFrame () (BodyStep.current frames frame machine) =
      ((⟨⟨frames⟩,FrameExit.afterRelevanceAt frames frame machine
        (thread.topUserRelevantFrame.getD frames.size)⟩ : WholeCall.State),.ok frame) := by
  have popped := FrameExit.pop_empty (TypedMachineBindings.retagHooks s.cfg.access s.cfg.retag)
    frames frame machine tracker {} tracked frameTracked rfl thread active
  have popEq : TypedMachineBindings.popRaw (TypedMachineBindings.retagHooks s.cfg.access s.cfg.retag)
      (BodyStep.current frames frame machine) =
      .ok frame (⟨⟨frames⟩,FrameExit.afterRelevanceAt frames frame machine
        (thread.topUserRelevantFrame.getD frames.size)⟩ : WholeCall.State) := by
    exact popped
  change MachineHooks.run (TypedMachineBindings.popRaw
    (TypedMachineBindings.retagHooks s.cfg.access s.cfg.retag)) _ = _
  simp only [MachineHooks.run,Call.run,popEq]

private theorem bound_copy (s : Static) (layout : LocalLayout) (place : MPlaceTy Provenance)
    (equal : place.layout = layout)
    (compatible : s.cfg.copy.compatible layout layout = .ok true)
    (padding : s.cfg.copy.hasPadding layout = .ok true) (sized : layout.layout.isSized = true) :
    copyRuntimePlace (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation s.cfg s.limits)).place
      (ExecutionMachine.withValidation s.cfg s.limits).copy () ⟨.immediate .uninit,layout⟩
      ⟨.memory place.mplace,place.layout⟩ true =
    copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,layout⟩
      ⟨.memory place.mplace,place.layout⟩ true := by
  funext state
  simp [ExecutionMachine.withValidation,ExecutionMachine.projectionHooks,TypedMachineBindings.bindValidation,
    copyRuntimePlace,copyRuntimePlaceNoValidate,equal,compatible,padding,sized,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

 theorem copy (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (positive : 0 < s.options.limits.validation)
    (state : WholeCall.State) (place : MPlaceTy Provenance)
    (layout : place.layout = s.abi.ret.layout)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (noGhost : state.machine.user.payload.ghost = false)
    (shallow : state.machine.user.payload.validation = .Shallow) :
    (control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩ (.memory place) state = (state,.ok ()) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have fields := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    leaves (remaining+1) metadata.construction s.cfg outer
  have compatible : s.cfg.copy.compatible s.abi.ret.layout s.abi.ret.layout = .ok true := by
    rw [fields.compatible]
    simp [CompilerCovariance.compatible,CompilerCovariance.relation,CompilerCovariance.relationWithIndex,
      profile.debug,Except.mapError,bind,Except.bind,pure,Except.pure]
  have padding : s.cfg.copy.hasPadding s.abi.ret.layout = .ok true := by
    rw [fields.padding]
    simp [CompilerCopy.hasPadding,metadata.unitBackend,pure,Except.pure]
  have eq := bound_copy s s.abi.ret.layout place layout compatible padding metadata.unitSized
  have safe := ReturnMemory.copy s metadata profile remaining capacity positive state place layout noMeta aligned noGhost shallow
  change MachineHooks.run (copyRuntimePlace _ _ () _ _ true) state = _
  simp only [RuntimeStackPlace.toRuntimePlace]
  rw [eq]
  simp only [MachineHooks.run,Call.run,safe]

 theorem cleanup (s : Static) (metadata : Metadata s)
    (remaining : Nat) (capacity : s.capacity = remaining+2)
    (frame : BodyStep.F) (state : WholeCall.State) (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind)
    (locals : frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}])
    (varargs : frame.vaList = #[]) :
    (control s).cleanupFrame () false frame state = (state,.ok .normal) := by
  let leaves := Configuration.leaves s.prepared s.options.place.debugAssertions
  have outer : EvalConfigurationCore.make s.prepared.compiler s.prepared.image s.bytes s.options leaves ()
      ((remaining+1)+1) = .ok s.cfg := by
    simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built
  have fields := ReturnMemory.fields_of_make s.prepared.compiler s.prepared.image s.bytes s.options
    leaves (remaining+1) metadata.construction s.cfg outer
  change MachineHooks.run (CallMachine.cleanup s.cfg.lifecycle () false frame) state = _
  simp [MachineHooks.run,Call.run,CallMachine.cleanup,continuation,locals,varargs,fields.afterPop,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

/-- Actual normal Return after the terminator hook, with exact relevance-cache
bookkeeping and caller continuation restoration. -/
 theorem core (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (positive : 0 < s.options.limits.validation)
    (older : Array BodyStep.F) (caller frame : BodyStep.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (body : Meaning.FrameMatches frame s.loaded) (location : frame.location = .mir ⟨0,1⟩)
    (locals : frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}])
    (noClocks : frame.extra.dataRace = none) (frameTracked : frame.extra.borrowTracker = some {})
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (place : MPlaceTy Provenance) (returnPlace : frame.returnPlace = .memory place)
    (layout : place.layout = s.abi.ret.layout)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind) (varargs : frame.vaList = #[])
    (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false
      (BodyStep.current (older.push caller) frame machine) =
      (ReturnContinuation.resume older caller
        (FrameExit.afterRelevanceAt (older.push caller) frame machine
          (thread.topUserRelevantFrame.getD (older.push caller).size)) target,.ok ()) := by
  let frames := older.push caller
  let finished := FrameExit.afterRelevanceAt frames frame machine (thread.topUserRelevantFrame.getD frames.size)
  have readEq := read s metadata profile remaining capacity frames frame machine locals noClocks
  have popEq := pop s frames frame machine tracker tracked frameTracked thread active
  have ghostAfter : finished.user.payload.ghost = false := by
    unfold finished FrameExit.afterRelevanceAt
    split <;> exact noGhost
  have shallowAfter : finished.user.payload.validation = .Shallow := by
    unfold finished FrameExit.afterRelevanceAt
    split <;> exact shallow
  have copyEq := copy s metadata profile remaining capacity positive
    (⟨⟨frames⟩,finished⟩ : WholeCall.State) place layout noMeta aligned ghostAfter shallowAfter
  have cleanupEq := cleanup s metadata remaining capacity frame (⟨⟨frames⟩,finished⟩ : WholeCall.State)
    target unwind continuation locals varargs
  have references := metadata.entry_references
  have block : frame.body.basicBlocks[0]? = some metadata.entry.blockId := by
    rw [body.1]; exact references.block
  have blockNode : frame.mirTables.blocks.lookup metadata.entry.blockId.index = .ok metadata.entry.block := by
    rw [body.2.2]; exact references.blockNode
  have cleanup := (block_observations s metadata).1
  rw [source]
  generalize actualControl : control s = hooks at readEq popEq copyEq cleanupEq ⊢
  cases hooks
  unfold ControlFlow.returnFromCurrentFrame
  simp only [BodyStep.current,LocalUnit.current,Stack.currentFrame?,Array.back?_push,
    location,block,blockNode,cleanup,Bool.false_bne,Bool.false_and,Bool.not_false,
    Bool.false_eq_true,bne_self_eq_false,Id.run,bind,Bind.bind,pure,Pure.pure,↓reduceIte]
  simp only [frames,finished,BodyStep.current,LocalUnit.current] at readEq popEq copyEq cleanupEq
  erw [readEq]
  erw [popEq]
  simp only [returnPlace]
  erw [copyEq]
  erw [cleanupEq]
  simp only [continuation]
  simpa only [frames,finished] using ReturnContinuation.returnToBlock_push older caller finished target

private theorem return_terminator (s : Static) (term : TerminatorNode) (kind : term.kind = .Return) :
    (ExecutionMachine.stepHooks s.cfg s.limits).terminator () term =
      (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false := by
  funext state
  unfold ExecutionMachine.stepHooks
  simp only [ControlFlow.evalTerminator,kind]
  rfl

/-- Compose the two separately proved machine operations at the actual fixed
Return instruction. These operation equations are internal proof edges, not
initial-input validity or metadata assumptions. -/
 theorem compose (s : Static) (metadata : Metadata s)
    (frames : Array BodyStep.F) (frame : BodyStep.F)
    (before afterHook : MachineHooks.MachineState MiriMemoryKind RootUser) (after : WholeCall.State)
    (body : Meaning.FrameMatches frame s.loaded) (location : frame.location = .mir ⟨0,1⟩)
    (hook : (ExecutionMachine.stepHooks s.cfg s.limits).beforeTerminator ()
      (BodyStep.current frames frame before) = (BodyStep.current frames frame afterHook,.ok ()))
    (returned : (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false
      (BodyStep.current frames frame afterHook) = (after,.ok ())) :
    ExecutionMachine.step s.cfg s.limits () (BodyStep.current frames frame before) = (after,.ok true) := by
  obtain ⟨cleanup, count, termNode, termAt, termKind⟩ := block_observations s metadata
  have term := return_terminator s termNode termKind
  have references := metadata.entry_references
  have block : frame.body.basicBlocks[0]? = some metadata.entry.blockId := by
    rw [body.1]; exact references.block
  have blockNode : frame.mirTables.blocks.lookup metadata.entry.blockId.index = .ok metadata.entry.block := by
    rw [body.2.2]; exact references.blockNode
  have terminator : frame.mirTables.terminators.lookup metadata.entry.block.terminator.index = .ok termNode := by
    rw [body.2.2]; exact termAt
  have absent : metadata.entry.block.statements[1]? = none :=
    Array.getElem?_eq_none (by omega)
  unfold ExecutionMachine.step
  generalize actualHooks : ExecutionMachine.stepHooks s.cfg s.limits = hooks at hook returned term ⊢
  cases hooks
  unfold Step.step
  simp only [BodyStep.current,LocalUnit.current,Stack.currentFrame?,Array.back?_push,
    location,block,blockNode,absent,terminator,Id.run,bind,Bind.bind,pure,Pure.pure]
  simp only [BodyStep.current,LocalUnit.current] at hook returned term
  rw [hook]
  rw [term]
  rw [returned]
  rfl

end EmptyFunction.ReturnStep
