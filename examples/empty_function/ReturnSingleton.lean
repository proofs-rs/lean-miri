import empty_function.ConcreteProtection
import empty_function.ReturnStep

/-! Singleton-protector adaptation of the shared unit Return operations. -/
namespace EmptyFunction.ReturnSingleton
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Internal composition for the common read/copy/cleanup/continuation stages.
The pop equation is discharged by a raw release theorem, never by validity. -/
 theorem core_from_pop (s : Static) (metadata : Metadata s) (profile : Profile s)
    (remaining : Nat) (capacity : s.capacity = remaining+2) (positive : 0 < s.options.limits.validation)
    (older : Array LocalUnit.F) (caller frame : LocalUnit.F)
    (before after : MachineHooks.MachineState MiriMemoryKind RootUser)
    (body : Meaning.FrameMatches frame s.loaded) (location : frame.location = .mir ⟨0,1⟩)
    (locals : frame.locals = #[{value := .live (.immediate .uninit),layout := some s.abi.ret.layout}])
    (noClocks : frame.extra.dataRace = none)
    (popped : (ReturnStep.control s).popFrame () (LocalUnit.current (older.push caller) frame before) =
      ((⟨⟨older.push caller⟩,after⟩ : WholeCall.State),.ok frame))
    (place : MPlaceTy Provenance) (returnPlace : frame.returnPlace = .memory place)
    (layout : place.layout = s.abi.ret.layout)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (target : BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwind) (varargs : frame.vaList = #[])
    (noGhost : after.user.payload.ghost = false) (shallow : after.user.payload.validation = .Shallow) :
    (ExecutionMachine.stepHooks s.cfg s.limits).returnFromCurrentFrame () false
      (LocalUnit.current (older.push caller) frame before) =
      (ReturnContinuation.resume older caller after target,.ok ()) := by
  have readEq := ReturnStep.read s metadata profile remaining capacity (older.push caller) frame before locals noClocks
  have copyEq := ReturnStep.copy s metadata profile remaining capacity positive
    (⟨⟨older.push caller⟩,after⟩ : WholeCall.State) place layout noMeta aligned noGhost shallow
  have cleanupEq := ReturnStep.cleanup s metadata remaining capacity frame
    (⟨⟨older.push caller⟩,after⟩ : WholeCall.State) target unwind continuation locals varargs
  have references := metadata.entry_references
  have block : frame.body.basicBlocks[0]? = some metadata.entry.blockId := by
    rw [body.1]; exact references.block
  have blockNode : frame.mirTables.blocks.lookup metadata.entry.blockId.index = .ok metadata.entry.block := by
    rw [body.2.2]; exact references.blockNode
  have blockCleanup := (ReturnStep.block_observations s metadata).1
  rw [ReturnStep.source]
  generalize actualControl : ReturnStep.control s = hooks at readEq popped copyEq cleanupEq ⊢
  cases hooks
  unfold ControlFlow.returnFromCurrentFrame
  simp only [BodyStep.current,LocalUnit.current,Stack.currentFrame?,Array.back?_push,location,block,blockNode,
    blockCleanup,Bool.false_bne,Bool.false_and,Bool.not_false,Bool.false_eq_true,
    bne_self_eq_false,Id.run,bind,Bind.bind,pure,Pure.pure,↓reduceIte]
  simp only [BodyStep.current,LocalUnit.current] at readEq popped copyEq cleanupEq
  erw [readEq]
  erw [popped]
  simp only [returnPlace]
  erw [copyEq]
  erw [cleanupEq]
  simp only [continuation]
  exact ReturnContinuation.returnToBlock_push older caller after target

 theorem pop (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F)
    (machine : MachineHooks.MachineState MiriMemoryKind RootUser) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (enabled : machine.borrowTracker = some (UnitRetag.allocatedTracker tracker room))
    (formed : TreeRuntimeInput.GlobalFormed tracker.global)
    (id : AllocId) (entry : InputDraft.Entry) (tree : BorrowTree)
    (released : tree.releaseProtector tracker.global.nextPointerTag
      (UnitRetag.registeredTracker (UnitRetag.allocatedTracker tracker room)
        tracker.global.nextPointerTag).global.protectedTags = ⟨tree,.Released⟩)
    (thread : Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    (ReturnStep.control s).popFrame ()
      (LocalUnit.current frames (UnitRetag.registeredFrame frame {} id tracker.global.nextPointerTag)
        {UnitRetag.registeredMachine machine (UnitRetag.allocatedTracker tracker room)
          tracker.global.nextPointerTag with memory := UnitRetag.replaceTree machine.memory id entry tree}) =
      ((⟨⟨frames⟩,FrameExit.afterRelevanceAt frames
          (UnitRetag.registeredFrame frame {} id tracker.global.nextPointerTag)
          {machine with memory := UnitRetag.replaceTree machine.memory id entry tree}
          (thread.topUserRelevantFrame.getD frames.size)⟩ : WholeCall.State),
        .ok (UnitRetag.registeredFrame frame {} id tracker.global.nextPointerTag)) := by
  let protectedFrame := UnitRetag.registeredFrame frame {} id tracker.global.nextPointerTag
  let after := {machine with memory := UnitRetag.replaceTree machine.memory id entry tree}
  have releaseEq := ConcreteProtection.release s metadata capacity frames frame machine tracker room enabled formed
    id entry tree released
  have activeAfter : after.threads.activeThread? = some thread := active
  have relevant := FrameExit.relevance_before_pop frames protectedFrame after thread activeAfter
  change MachineHooks.run (TypedMachineBindings.popRaw
    (TypedMachineBindings.retagHooks s.cfg.access s.cfg.retag)) _ = _
  unfold TypedMachineBindings.popRaw
  simp only [TypedMachineBindings.retagHooks]
  simp only [MachineHooks.run,Call.run,bind,Bind.bind,EStateM.bind]
  rw [releaseEq]
  simp only [LocalUnit.current,FrameExit.withCurrent,protectedFrame,after] at relevant ⊢
  rw [relevant]
  simp [LocalUnit.current,FrameExit.withCurrent,protectedFrame,after,Stack.popFrame,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
    set,MonadStateOf.set,EStateM.set,pure,Pure.pure,EStateM.pure,Except.pure]

end EmptyFunction.ReturnSingleton
