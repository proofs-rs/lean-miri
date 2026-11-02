import Miri.Interpreter.CallMachine
import Lean

/-! Production frame exit for a frame with no owned protectors. This covers
the local unit destination specialization; a memory destination may add a
protector and must first use its corresponding release theorem. -/
namespace EmptyFunction.FrameExit
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
set_option autoImplicit false
variable {K U C Other : Type}

abbrev F := Frame Provenance LocalLayout MachineHooks.FrameExtra

def withCurrent (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U) :
    MachineHooks.State K U := ⟨⟨frames.push frame⟩,machine⟩

def afterRelevance (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) : MachineHooks.MachineState K U :=
  let cache := FrameRelevance.computeTop ⟨frames.push frame⟩ 1
  {machine with threads := {machine.threads with threads := machine.threads.threads.mapIdx fun index thread =>
    if index == machine.threads.activeThread.toNat then {thread with topUserRelevantFrame := cache} else thread}}

def afterRelevanceAt (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (index : Nat) :=
  if index = frames.size then afterRelevance frames frame machine else machine

/-- Pure computation of the optional relevance-cache index on a nonempty stack. -/
theorem top_nonempty (frames : Array F) (frame : F) (cached : Option Nat) :
    FrameRelevance.top ⟨frames.push frame⟩ cached = some (cached.getD frames.size) := by
  cases cached <;> simp [FrameRelevance.top]

/-- Empty protector ownership makes the actual release loop an identity,
without any assumption about an allocation or ensure callback succeeding. -/
theorem release_empty [DecidableEq K]
    (ensure : AllocId → MachineHooks.M K U Unit) (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[]) :
    MachineHooks.beforeStackPopWithEnsure ensure (withCurrent frames frame machine) =
      .ok () (withCurrent frames frame machine) := by
  simp [MachineHooks.beforeStackPopWithEnsure, withCurrent, tracked,
    MachineHooks.currentFrame, Stack.currentFrame?, frameTracked, empty,
    Miri.TreeBorrows.GlobalState.endCall,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    set, MonadStateOf.set, EStateM.set, pure, Pure.pure, EStateM.pure]
  change {machine with borrowTracker := some tracker} = machine
  rw [← tracked]

-- Proof automation for the two private source helpers; no replacement
-- callback or unchecked execution is introduced. Uniqueness is checked.
open Lean Elab Tactic in
elab "unfold_relevance_helper " suffix:str : tactic => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix.getString then some name else none
  match names with
  | [name] => evalTactic (← `(tactic| unfold $(mkIdent name)))
  | _ => throwError "expected one source helper ending in {suffix.getString}"

private theorem relevance_current (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top ⟨frames.push frame⟩ thread.topUserRelevantFrame = some frames.size) :
    FrameRelevance.beforeStackPop (withCurrent frames frame machine) =
      .ok () (withCurrent frames frame (afterRelevance frames frame machine)) := by
  unfold FrameRelevance.beforeStackPop
  unfold_relevance_helper ".FrameRelevance.active"
  simp only [withCurrent, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, active, pure, EStateM.pure, top]
  simp only [Array.size_push, Nat.add_sub_cancel, beq_self_eq_true, ↓reduceIte]
  unfold_relevance_helper ".FrameRelevance.setCache"
  unfold_relevance_helper ".FrameRelevance.active"
  simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, active,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure, EStateM.pure,
    afterRelevance]

/-- Recompute the cache exactly when it names the departing frame. A prior
caller cache is retained; no particular caller relevance or cache is required. -/
theorem relevance_before_pop (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread) :
    FrameRelevance.beforeStackPop (withCurrent frames frame machine) =
      .ok () (withCurrent frames frame (afterRelevanceAt frames frame machine
        (thread.topUserRelevantFrame.getD frames.size))) := by
  have top := top_nonempty frames frame thread.topUserRelevantFrame
  by_cases same : thread.topUserRelevantFrame.getD frames.size = frames.size
  · simpa only [afterRelevanceAt, same, ↓reduceIte] using
      relevance_current frames frame machine thread active (by simpa only [same] using top)
  · unfold FrameRelevance.beforeStackPop
    unfold_relevance_helper ".FrameRelevance.active"
    simp [withCurrent, get, getThe, MonadStateOf.get, EStateM.get,
      bind, EStateM.bind, active, pure, EStateM.pure, top, same, afterRelevanceAt]

/-- The real raw-pop pipeline for the empty owned-protector branch. Runtime
inputs describe only actual current data; no stage-success premise is required. -/
theorem pop_empty [DecidableEq K] (retag : TypedRetag.Hooks K U)
    (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    TypedMachineBindings.popRaw retag (withCurrent frames frame machine) =
      .ok frame (⟨⟨frames⟩,afterRelevanceAt frames frame machine
        (thread.topUserRelevantFrame.getD frames.size)⟩ : MachineHooks.State K U) := by
  unfold TypedMachineBindings.popRaw
  simp only [bind, EStateM.bind]
  rw [release_empty retag.ensureTreeExtra frames frame machine tracker borrowFrame tracked frameTracked empty]
  simp only
  rw [relevance_before_pop frames frame machine thread active]
  simp [withCurrent, get, getThe, MonadStateOf.get, EStateM.get,
    Stack.popFrame, Array.back?_push, Array.pop_push,
    EStateM.bind, set, MonadStateOf.set, EStateM.set,
    pure, EStateM.pure, Except.pure]

/-- With no allocated local or vararg, cleanup performs no deallocation. The
actual normal after-stack-pop implementation returns normal without invoking
unwind host operations; it does not require a hypothetical success hook. -/
theorem cleanup_unit (lifecycle : CallMachine.Lifecycle K U C)
    (unwindHooks : Unwind.Hooks K U C Other) (choice : C)
    (frame : F) (state : MachineHooks.State K U)
    (ret : Option BasicBlockId) (unwind : UnwindAction)
    (continuation : frame.returnContinuation = .goto ret unwind)
    (slot : LocalState Provenance LocalLayout)
    (locals : frame.locals = #[slot])
    (immediate : ∃ value,slot.value = .live (.immediate value))
    (varargs : frame.vaList = #[]) :
    CallMachine.cleanup (CallMachine.withUnwind lifecycle unwindHooks) choice false frame state =
      .ok .normal state := by
  obtain ⟨value,hvalue⟩ := immediate
  simp [CallMachine.cleanup, continuation, locals, varargs,
    hvalue, CallMachine.withUnwind, Unwind.afterStackPop,
    bind, EStateM.bind, pure, EStateM.pure]

/-- Relevance bookkeeping preserves all physical memory exactly. -/
theorem afterRelevanceAt_memory (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (index : Nat) :
    (afterRelevanceAt frames frame machine index).memory = machine.memory := by
  unfold afterRelevanceAt
  split <;> rfl

/-- Fields of unrelated threads are not rewritten by relevance bookkeeping. -/
theorem afterRelevanceAt_other_thread (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (index other : Nat)
    (present : other < machine.threads.threads.length)
    (different : other ≠ machine.threads.activeThread.toNat) :
    (afterRelevanceAt frames frame machine index).threads.threads[other]? =
      machine.threads.threads[other]? := by
  by_cases same : index=frames.size
  · simp [afterRelevanceAt,same,afterRelevance,different,present]
  · simp [afterRelevanceAt,same]

end EmptyFunction.FrameExit

open Lean Elab Command in
run_cmd do
  for name in #[``EmptyFunction.FrameExit.release_empty, ``EmptyFunction.FrameExit.relevance_before_pop,
      ``EmptyFunction.FrameExit.pop_empty, ``EmptyFunction.FrameExit.cleanup_unit,
      ``EmptyFunction.FrameExit.afterRelevanceAt_memory, ``EmptyFunction.FrameExit.afterRelevanceAt_other_thread] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved empty_function frame-exit axiom {dependency}"
