import empty_function.LocalReturnCopy
import empty_function.ReturnStep
namespace EmptyFunction.LocalReturn
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false

private theorem bound_copy (s : Static) (layout : LocalLayout) (dest : RuntimePlace Provenance)
    (equal : dest.layout = layout)
    (compatible : s.cfg.copy.compatible layout layout = .ok true)
    (padding : s.cfg.copy.hasPadding layout = .ok true) (sized : layout.layout.isSized = true) :
    copyRuntimePlace (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation s.cfg s.limits)).place
      (ExecutionMachine.withValidation s.cfg s.limits).copy () ⟨.immediate .uninit,layout⟩ dest true =
      copyRuntimePlace s.cfg.projection.place s.cfg.copy () ⟨.immediate .uninit,layout⟩ dest true := by
  funext state
  simp [ExecutionMachine.withValidation,ExecutionMachine.projectionHooks,TypedMachineBindings.bindValidation,
    copyRuntimePlace,copyRuntimePlaceNoValidate,equal,compatible,padding,sized,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]

 theorem copy (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (positive : 0 < s.options.limits.validation)
    (older : Array LocalUnit.F) (caller : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (id : MIR.LocalId)
    (slot : LocalState Provenance LocalLayout) (atSlot : caller.locals[id]? = some slot)
    (live : slot.value = .live (.immediate .uninit)) (cache : slot.layout = some s.abi.ret.layout)
    (noClocks : caller.extra.dataRace = none) (noGhost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow) :
    (ReturnStep.control s).copyReturn () ⟨.immediate .uninit,s.abi.ret.layout⟩
      (.frameLocal older.size id none s.abi.ret.layout caller.localsIdentity)
      (LocalUnit.current older caller machine) = (LocalUnit.current older caller machine,.ok ()) := by
  have source := BodyPlaceDictionaries.fields_of_make s.prepared.compiler s.prepared.image s.bytes (EmptyFunction.Configuration.proofOptions s.options)
    (Configuration.leaves s.prepared s.options.place.debugAssertions) (remaining+1) metadata.construction s.cfg
    (by simpa only [Configuration.rootConfig,capacity,Nat.add_assoc] using s.built)
  have compatible : s.cfg.copy.compatible s.abi.ret.layout s.abi.ret.layout = .ok true := by
    rw [source.compatible]
    simp [CompilerCovariance.compatible,CompilerCovariance.relation,CompilerCovariance.relationWithIndex,
      profile.debug,Except.mapError,bind,Except.bind,pure,Except.pure]
  have padding : s.cfg.copy.hasPadding s.abi.ret.layout = .ok true := by
    rw [source.padding]
    simp [CompilerCopy.hasPadding,metadata.unitBackend,pure,Except.pure]
  have eq := bound_copy s s.abi.ret.layout (LocalReturnCopy.destination older caller id s.abi.ret.layout)
    rfl compatible padding metadata.unitSized
  have safe := LocalReturnCopy.unit_allow s metadata profile true remaining capacity positive older caller machine
    id slot atSlot live cache noClocks noGhost shallow
  change MachineHooks.run (copyRuntimePlace _ _ () _ _ true) (LocalUnit.current older caller machine) = _
  simp only [RuntimeStackPlace.toRuntimePlace]
  change MachineHooks.run (copyRuntimePlace _ _ () _ (LocalReturnCopy.destination older caller id s.abi.ret.layout) true) _ = _
  rw [eq]
  simp only [MachineHooks.run,Call.run,safe]

 theorem core (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (positive : 0 < s.options.limits.validation)
    (older : Array LocalUnit.F) (caller frame : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (body : frame.body = s.loaded.body) (location : frame.location = .mir ⟨0,1⟩)
    (locals : frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}])
    (noClocks : frame.extra.dataRace = none) (frameTracked : frame.extra.borrowTracker = some {})
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (thread : Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (id : MIR.LocalId) (slot : LocalState Provenance LocalLayout)
    (atSlot : caller.locals[id]? = some slot) (live : slot.value = .live (.immediate .uninit))
    (cache : slot.layout = some s.abi.ret.layout) (callerNoClocks : caller.extra.dataRace = none)
    (returnPlace : frame.returnPlace = .frameLocal older.size id none s.abi.ret.layout caller.localsIdentity)
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind) (varargs : frame.vaList = #[])
    (noGhost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow) :
    let finished := FrameExit.afterRelevanceAt (older.push caller) frame machine
      (thread.topUserRelevantFrame.getD (older.push caller).size)
    (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false
      (LocalUnit.current (older.push caller) frame machine) =
      (ReturnContinuation.resume older caller finished target,.ok ()) := by
  let finished := FrameExit.afterRelevanceAt (older.push caller) frame machine
    (thread.topUserRelevantFrame.getD (older.push caller).size)
  have ghost : finished.user.payload.ghost = false := by
    unfold finished FrameExit.afterRelevanceAt FrameExit.afterRelevance
    split <;> exact noGhost
  have shallowAfter : finished.user.payload.validation = .Shallow := by
    unfold finished FrameExit.afterRelevanceAt FrameExit.afterRelevance
    split <;> exact shallow
  have readEq := ReturnStep.read s metadata profile remaining capacity (older.push caller) frame machine locals noClocks
  have popEq := ReturnStep.pop s (older.push caller) frame machine tracker tracked frameTracked thread active
  have copyEq := copy s metadata profile remaining capacity positive older caller finished id slot atSlot live cache
    callerNoClocks ghost shallowAfter
  have cleanupEq := ReturnStep.cleanup s metadata remaining capacity frame (LocalUnit.current older caller finished)
    target unwind continuation locals varargs
  have block : frame.body.basicBlocks[0]? = some Program.block := by rw [body,metadata.body]; rfl
  rw [ReturnStep.source]
  generalize actualControl : ReturnStep.control s = hooks at readEq popEq copyEq cleanupEq ⊢
  cases hooks
  unfold ControlFlow.returnFromCurrentFrame
  simp only [BodyStep.current,LocalUnit.current,Stack.currentFrame?,Array.back?_push,location,block,
    Program.no_cleanup,Bool.false_bne,Bool.false_and,Bool.not_false,Bool.false_eq_true,
    bne_self_eq_false,Id.run,bind,Bind.bind,pure,Pure.pure,↓reduceIte]
  simp only [BodyStep.current,LocalUnit.current,finished] at readEq popEq copyEq cleanupEq
  erw [readEq]
  erw [popEq]
  simp only [returnPlace]
  erw [copyEq]
  erw [cleanupEq]
  simp only [continuation]
  exact ReturnContinuation.returnToBlock_push older caller finished target

end EmptyFunction.LocalReturn
