import empty_function.LocalInit
namespace EmptyFunction.LocalCachedPush
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.Concurrency
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.Configuration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 800000
set_option linter.unusedSimpArgs false
def cachedState (s : Static) (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) : State :=
  LocalUnit.current older (LocalImmediate.cached destination.caller destination.localId destination.slot
    destination.baseLayout bound) p.before.machine

theorem push_cached (s : Static) (metadata : Metadata s) (profile : Profile s)
    (p : Packet) (runtime : RuntimeProfile s p) (input : InputDraft.CurrentInputDraft s p) (capacity : 0 < s.capacity)
    (destination : InputDraft.LocalDestination s p input.tracker)
    (older : Array LocalUnit.F) (original : p.before.stack.frames = older.push destination.caller)
    (bound : destination.localId < destination.caller.locals.size)
    (continuation : ReturnContinuation) :
    ∃ frame machine,
      (ExecutionMachine.callHooks s.cfg s.limits).pushRaw () s.functionInstance s.loaded
        p.destination continuation (cachedState s p input.tracker destination older bound) =
        .ok () (⟨⟨(cachedState s p input.tracker destination older bound).stack.frames.push frame⟩,machine⟩ : State) ∧
      (∃ previous, machine = FrameRelevance.pushedMachine (cachedState s p input.tracker destination older bound).stack.frames frame previous
        (s.cfg.lifecycle.freshLocalsIdentity (cachedState s p input.tracker destination older bound).machine).1) ∧
      frame.extra.borrowTracker = some {} ∧ frame.extra.dataRace = none ∧
      frame.body = s.loaded.body ∧ frame.bodyIdentity = s.loaded.identity ∧
      frame.functionInstance = s.functionInstance ∧ frame.location = .unwinding metadata.preamble ∧
      frame.returnContinuation = continuation ∧ frame.returnPlace = p.destination ∧
      frame.locals = #[{value := .dead,layout := none}] ∧ frame.vaList = #[] ∧
      frame.trackCallerArg = none ∧
      machine.borrowTracker = (cachedState s p input.tracker destination older bound).machine.borrowTracker ∧ machine.dataRace = none := by
  have fields := MetadataBinding.fields s metadata capacity
  obtain ⟨definitionIndex, definition, definitionResolved, definitionAt⟩ := metadata.frameDefinition
  let frame := EmptyFunction.Init.created s.cfg.lifecycle (cachedState s p input.tracker destination older bound) s.loaded s.functionInstance p.destination
    continuation metadata.preamble s.prepared.compiler.lifecycle.frames s.options.userRelevantCrates definition
  let machine := (s.cfg.lifecycle.freshLocalsIdentity (cachedState s p input.tracker destination older bound).machine).1
  have threads : machine.threads = (cachedState s p input.tracker destination older bound).machine.threads := by
    simp only [machine, fields.freshLocalsIdentity]
  have active : machine.threads.activeThread? = some input.thread := by
    rw [threads]
    exact input.active
  have select : ∃ index old,
      FrameRelevance.top ⟨(cachedState s p input.tracker destination older bound).stack.frames.push frame⟩ input.thread.topUserRelevantFrame = some index ∧
      ((cachedState s p input.tracker destination older bound).stack.frames.push frame)[index]? = some old := by
    cases cache : input.thread.topUserRelevantFrame with
    | none =>
      refine ⟨(cachedState s p input.tracker destination older bound).stack.frames.size,frame,?_,?_⟩
      · simp [FrameRelevance.top,cache]
      · simp
    | some index =>
      have bounded : index < (cachedState s p input.tracker destination older bound).stack.frames.size := by
        have bound := input.relevance index cache
        simpa only [original,cachedState,LocalUnit.current,Array.size_push] using bound
      refine ⟨index,(cachedState s p input.tracker destination older bound).stack.frames[index],?_,?_⟩
      · simp [FrameRelevance.top,cache]
      · rw [Array.getElem?_push, if_neg (Nat.ne_of_lt bounded), Array.getElem?_eq_getElem bounded]
  obtain ⟨index,old,cached,selected⟩ := select
  have pushed := EmptyFunction.Init.push_raw s.cfg.lifecycle (cachedState s p input.tracker destination older bound) s.loaded s.functionInstance p.destination
    continuation metadata.preamble s.prepared.compiler.lifecycle.frames s.options.userRelevantCrates definition definitionIndex
    s.prepared.compiler.lifecycle.lifecycle metadata.loweredBody fields.frameCompiler fields.preambleSpan
    fields.requiredConstants metadata.frameInlineAttribute metadata.frameTrackCaller definitionResolved definitionAt
    metadata.lifecycleBody metadata.bodyContents metadata.lifecycleRow input.thread index active old cached selected
  refine ⟨frame,FrameRelevance.pushedMachine (cachedState s p input.tracker destination older bound).stack.frames frame old machine,?_,⟨old,rfl⟩,?_,?_,?_⟩
  · change CallMachine.pushRaw s.cfg.lifecycle s.cfg.compiler.debugAssertions s.functionInstance s.loaded
      p.destination continuation (cachedState s p input.tracker destination older bound) = _
    rw [fields.debug,profile.debug]
    exact pushed
  · simp only [frame,EmptyFunction.Init.created,CompilerFrameMetadata.resolvedFrame]
    have enabled := input.world.enabled
    simp only [machine,fields.freshLocalsIdentity] at *
    simp [enabled,cachedState,LocalUnit.current]
  · simp [frame,EmptyFunction.Init.created,CompilerFrameMetadata.resolvedFrame, fields.freshLocalsIdentity,cachedState,LocalUnit.current,runtime.noRace]
  · have count : s.loaded.body.locals.size = 1 := by rw [metadata.body]; exact Program.one_local
    simp only [frame,EmptyFunction.Init.created,CompilerFrameMetadata.resolvedFrame,EmptyFunction.Init.raw,Frame.create,count,
      Array.replicate_succ,Array.replicate_zero]
    simp [FrameRelevance.pushedMachine,machine,fields.freshLocalsIdentity,cachedState,LocalUnit.current,runtime.noRace]
    split <;> constructor <;> rfl


end EmptyFunction.LocalCachedPush
