import duplicate_prefix.RootOperandCopy
import duplicate_prefix.AllocationCopy
import Miri.Interpreter.ExecutionControl

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.GenericPopFrame
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
open DuplicatePrefix.AllocationCopy

def afterRelevance (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) : MachineHooks.MachineState K U :=
  let cache := FrameRelevance.computeTop ⟨frames.push frame⟩ 1
  {machine with threads := {machine.threads with threads := machine.threads.threads.mapIdx fun index thread =>
    if index == machine.threads.activeThread.toNat then {thread with topUserRelevantFrame := cache} else thread}}

/-- The actual relevance suffix runs while the popped frame is still current. -/
theorem relevance_before_pop
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (thread : ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top ⟨frames.push frame⟩ thread.topUserRelevantFrame = some frames.size) :
    FrameRelevance.beforeStackPop (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame (afterRelevance frames frame machine)) := by
  unfold FrameRelevance.beforeStackPop
  unfold_internal ".FrameRelevance.active"
  simp only [Storage.withCurrent, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, active, pure, EStateM.pure, top]
  simp only [Array.size_push, Nat.add_sub_cancel, beq_self_eq_true, ↓reduceIte]
  unfold_internal ".FrameRelevance.setCache"
  unfold_internal ".FrameRelevance.active"
  simp [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, active,
    modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure, EStateM.pure,
    afterRelevance, Storage.withCurrent]

/-- The source raw pop releases protectors, updates relevance, and only then
removes the frame. The release transition is supplied by its exact source hook. -/
theorem pop_after_release [DecidableEq K]
    (retag : TypedRetag.Hooks K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (before released : MachineHooks.MachineState K U) (thread : ThreadRecord)
    (release : MachineHooks.beforeStackPopWithEnsure retag.ensureTreeExtra
      (Storage.withCurrent frames frame before) = .ok () (Storage.withCurrent frames frame released))
    (active : released.threads.activeThread? = some thread)
    (top : FrameRelevance.top ⟨frames.push frame⟩ thread.topUserRelevantFrame = some frames.size) :
    TypedMachineBindings.popRaw retag (Storage.withCurrent frames frame before) =
      .ok frame (⟨⟨frames⟩, afterRelevance frames frame released⟩ : MachineHooks.State K U) := by
  unfold TypedMachineBindings.popRaw
  simp only [bind, EStateM.bind]
  rw [release]
  simp only
  rw [relevance_before_pop frames frame released thread active top]
  simp [Storage.withCurrent, get, getThe, MonadStateOf.get, EStateM.get,
    Stack.popFrame, Array.back?_push, Array.pop_push,
    bind, EStateM.bind, set, MonadStateOf.set, EStateM.set,
    pure, EStateM.pure, Except.pure]

/-- No protector is released or allocated for an empty frame-owned tag list. -/
theorem release_empty [DecidableEq K]
    (ensure : AllocId → MachineHooks.M K U Unit)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[]) :
    MachineHooks.beforeStackPopWithEnsure ensure (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
  simp [MachineHooks.beforeStackPopWithEnsure, Storage.withCurrent, tracked,
    MachineHooks.currentFrame, Stack.currentFrame?, frameTracked, empty,
    Miri.TreeBorrows.GlobalState.endCall, Array.forIn_toList,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind,
    set, MonadStateOf.set, EStateM.set, pure, Pure.pure, EStateM.pure]
  change {machine with borrowTracker := some tracker} = machine
  rw [← tracked]

/-- A more relevant caller remains cached when the returning helper is not
itself the top user-relevant frame. -/
theorem relevance_before_pop_earlier
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (thread : ThreadRecord) (index : Nat)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top ⟨frames.push frame⟩ thread.topUserRelevantFrame = some index)
    (different : index ≠ frames.size) :
    FrameRelevance.beforeStackPop (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine) := by
  unfold FrameRelevance.beforeStackPop
  unfold_internal ".FrameRelevance.active"
  simp [Storage.withCurrent, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, active, pure, EStateM.pure, top, different]

def afterRelevanceAt (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (index : Nat) :=
  if index = frames.size then afterRelevance frames frame machine else machine

theorem relevance_before_pop_at
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (thread : ThreadRecord) (index : Nat)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top ⟨frames.push frame⟩ thread.topUserRelevantFrame = some index) :
    FrameRelevance.beforeStackPop (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame (afterRelevanceAt frames frame machine index)) := by
  by_cases same : index = frames.size
  · subst index
    simpa only [afterRelevanceAt, ↓reduceIte] using relevance_before_pop frames frame machine thread active top
  · simpa only [afterRelevanceAt, same, ↓reduceIte] using
      relevance_before_pop_earlier frames frame machine thread index active top same

theorem pop_after_release_at [DecidableEq K]
    (retag : TypedRetag.Hooks K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (before released : MachineHooks.MachineState K U) (thread : ThreadRecord) (index : Nat)
    (release : MachineHooks.beforeStackPopWithEnsure retag.ensureTreeExtra
      (Storage.withCurrent frames frame before) = .ok () (Storage.withCurrent frames frame released))
    (active : released.threads.activeThread? = some thread)
    (top : FrameRelevance.top ⟨frames.push frame⟩ thread.topUserRelevantFrame = some index) :
    TypedMachineBindings.popRaw retag (Storage.withCurrent frames frame before) =
      .ok frame (⟨⟨frames⟩, afterRelevanceAt frames frame released index⟩ : MachineHooks.State K U) := by
  unfold TypedMachineBindings.popRaw
  simp only [bind, EStateM.bind]
  rw [release]
  simp only
  rw [relevance_before_pop_at frames frame released thread index active top]
  simp [Storage.withCurrent, get, getThe, MonadStateOf.get, EStateM.get,
    Stack.popFrame, Array.back?_push, Array.pop_push,
    bind, EStateM.bind, set, MonadStateOf.set, EStateM.set,
    pure, EStateM.pure, Except.pure]

theorem pop_empty [DecidableEq K]
    (retag : TypedRetag.Hooks K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : ThreadRecord) (index : Nat)
    (active : machine.threads.activeThread? = some thread)
    (top : FrameRelevance.top ⟨frames.push frame⟩ thread.topUserRelevantFrame = some index) :
    TypedMachineBindings.popRaw retag (Storage.withCurrent frames frame machine) =
      .ok frame (⟨⟨frames⟩, afterRelevanceAt frames frame machine index⟩ : MachineHooks.State K U) :=
  pop_after_release_at retag frames frame machine machine thread index
    (release_empty retag.ensureTreeExtra frames frame machine tracker borrowFrame tracked frameTracked empty) active top


theorem top_nonempty
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (cached : Option Nat) :
    FrameRelevance.top ⟨frames.push frame⟩ cached = some (cached.getD frames.size) := by
  cases cached <;> simp [FrameRelevance.top]

/-- Empty-frame pop needs only an actual active thread; the source cache branch
is computed from its stored optional index. -/
theorem pop_empty_active [DecidableEq K]
    (retag : TypedRetag.Hooks K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) (borrowFrame : Miri.TreeBorrows.FrameState)
    (tracked : machine.borrowTracker = some tracker)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread) :
    TypedMachineBindings.popRaw retag (Storage.withCurrent frames frame machine) =
      .ok frame (⟨⟨frames⟩,
        afterRelevanceAt frames frame machine (thread.topUserRelevantFrame.getD frames.size)⟩ : MachineHooks.State K U) :=
  pop_empty retag frames frame machine tracker borrowFrame tracked frameTracked empty thread _ active
    (top_nonempty frames frame thread.topUserRelevantFrame)


open Lean Elab Command in
run_cmd do
  for declaration in [``top_nonempty, ``pop_empty_active, ``release_empty, ``relevance_before_pop_earlier, ``relevance_before_pop_at, ``pop_after_release_at, ``pop_empty, ``relevance_before_pop, ``pop_after_release] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
end DuplicatePrefix.GenericPopFrame
