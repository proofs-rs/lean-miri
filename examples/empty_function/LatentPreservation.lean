import empty_function.LatentExecution
import empty_function.IntegerThreads
namespace EmptyFunction.LatentPreservation
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open EmptyFunction.WholeCall EmptyFunction.Configuration EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

private theorem erase_cache (threads : List ThreadRecord) (active : Nat) (cache : Option Nat) :
    (threads.mapIdx (fun index thread => if index == active then
      {thread with topUserRelevantFrame := cache} else thread)).map
        (fun thread => {thread with topUserRelevantFrame := none}) =
      threads.map (fun thread => {thread with topUserRelevantFrame := none}) := by
  apply List.ext_getElem?
  intro index
  simp only [List.getElem?_map,List.getElem?_mapIdx]
  cases found : threads[index]? with
  | none => rfl
  | some thread => by_cases same : index = active <;> simp [same]

private theorem other_cache (threads : List ThreadRecord) (active : Nat) (cache : Option Nat)
    (index : Nat) (different : index ≠ active) :
    (threads.mapIdx (fun i thread => if i == active then
      {thread with topUserRelevantFrame := cache} else thread))[index]? = threads[index]? := by
  simp [List.getElem?_mapIdx,different]

/-- Only the active thread's relevance cache can change between the actual
push and pop; the lazy allocation fold preserves the entire pushed manager. -/
private theorem thread_projections (p : Packet) (pushed previous popped : LocalUnit.F)
    (machine : ChoiceExecution.S)
    (threads : machine.threads = (FrameRelevance.pushedMachine p.before.stack.frames pushed previous p.before.machine).threads)
    (index : Nat) :
    Preservation.OtherThreads p.before
      (⟨p.before.stack,FrameExit.afterRelevanceAt p.before.stack.frames popped machine index⟩ : State) ∧
    Preservation.ThreadContext p.before
      (⟨p.before.stack,FrameExit.afterRelevanceAt p.before.stack.frames popped machine index⟩ : State) := by
  unfold Preservation.OtherThreads Preservation.ThreadContext
  by_cases push : pushed.extra.userRelevance >= previous.extra.userRelevance <;>
    by_cases pop : index = p.before.stack.frames.size <;>
    simp only [FrameExit.afterRelevanceAt,pop,FrameExit.afterRelevance,↓reduceIte]
  all_goals
    simp only [threads,FrameRelevance.pushedMachine,push,↓reduceIte,Preservation.eraseThreadRelevance]
    constructor
    · refine ⟨True.intro,?_,?_⟩
      · simp
      · intro i different
        simp only [other_cache _ _ _ i different]
    · simp only [erase_cache]

/-- The eleven observable fields at the real resumed caller. The input facts
come from actual lazy protection/release; host terminator accounting and
relevance-cache changes are discharged here. -/
theorem finish (s : Static) (p : Packet) (input : InputDraft.CurrentInputDraft s p)
    (destination : MPlaceTy Provenance) (encoding : p.destination = .memory destination)
    (older : Array LocalUnit.F) (original : p.before.stack.frames = older.push input.caller)
    (pushed previous popped : LocalUnit.F) (machine : ChoiceExecution.S) (index : Nat)
    (oldLive : Preservation.OriginalLiveAllocations p.before (LocalUnit.current p.before.stack.frames popped machine))
    (protectors : Preservation.ExistingProtectors p.before (LocalUnit.current p.before.stack.frames popped machine))
    (roots : Preservation.ExistingRoots p.before (LocalUnit.current p.before.stack.frames popped machine))
    (addresses : Preservation.ExistingAddressFacts p.before (LocalUnit.current p.before.stack.frames popped machine))
    (threads : machine.threads = (FrameRelevance.pushedMachine p.before.stack.frames pushed previous p.before.machine).threads)
    (view : RelocationContext.view machine.user.payload = RelocationContext.view p.before.machine.user.payload) :
    let term := (TerminatorStep.after (LocalUnit.current p.before.stack.frames popped machine)).machine
    let final := ReturnContinuation.resume older input.caller
      (FrameExit.afterRelevanceAt p.before.stack.frames popped term index) p.returnBlock
    Preservation.Preserves s p final := by
  dsimp only
  let term := (TerminatorStep.after (LocalUnit.current p.before.stack.frames popped machine)).machine
  let final := ReturnContinuation.resume older input.caller
      (FrameExit.afterRelevanceAt p.before.stack.frames popped term index) p.returnBlock
  have returned : Returned p final := by
    refine ⟨?_,?_,input.caller,{input.caller with location := .mir ⟨p.returnBlock,0⟩},input.current,?_,rfl,rfl,rfl,rfl,rfl⟩
    · simp [final,ReturnContinuation.resume,original]
    · simp [final,ReturnContinuation.resume,original]
    · simp [final,ReturnContinuation.resume,Stack.currentFrame?]
  have projections := thread_projections p pushed previous popped term threads index
  refine ⟨returned,?_,?_,projections.1,?_,?_,?_,projections.2,?_,?_,?_⟩
  · unfold Preservation.OriginalLiveAllocations at *
    dsimp only [final,ReturnContinuation.resume,FrameExit.afterRelevanceAt]
    split <;> simpa only [FrameExit.afterRelevance,term,TerminatorStep.after,LocalUnit.current,TerminatorStep.setControl] using oldLive
  · unfold Preservation.ExistingProtectors at *
    dsimp only [final,ReturnContinuation.resume,FrameExit.afterRelevanceAt]
    split <;> simpa only [FrameExit.afterRelevance,term,TerminatorStep.after,LocalUnit.current,TerminatorStep.setControl] using protectors
  · intro old caller before after
    have oldEq : old = input.caller := Option.some.inj (before.symm.trans input.current)
    have callerEq : caller = {input.caller with location := .mir ⟨p.returnBlock,0⟩} :=
      Option.some.inj (after.symm.trans (ReturnContinuation.resume_current _ _ _ _))
    subst old;subst caller
    exact ⟨rfl,fun _ _ => rfl⟩
  · simp [Preservation.SelectedProjectedContents,encoding]
  · intro old caller before after
    have oldEq : old = input.caller := Option.some.inj (before.symm.trans input.current)
    have callerEq : caller = {input.caller with location := .mir ⟨p.returnBlock,0⟩} :=
      Option.some.inj (after.symm.trans (ReturnContinuation.resume_current _ _ _ _))
    subst old;subst caller
    rfl
  · unfold Preservation.ExistingAddressFacts at *
    dsimp only [final,ReturnContinuation.resume,FrameExit.afterRelevanceAt]
    split <;> simpa only [FrameExit.afterRelevance,term,TerminatorStep.after,LocalUnit.current,TerminatorStep.setControl] using addresses
  · have fields : machine.user.payload.payload.user.types = p.before.machine.user.payload.payload.user.types ∧
        machine.user.payload.ghost = p.before.machine.user.payload.ghost ∧
        machine.user.payload.validation = p.before.machine.user.payload.validation ∧
        machine.user.payload.payload.user.host.ioSources = p.before.machine.user.payload.payload.user.host.ioSources ∧
        machine.user.payload.payload.user.host.control = p.before.machine.user.payload.payload.user.host.control := by
      simpa only [RelocationContext.view,Prod.mk.injEq] using view
    unfold Preservation.RuntimeContext
    dsimp only [final,ReturnContinuation.resume,FrameExit.afterRelevanceAt]
    split <;> simp only [FrameExit.afterRelevance,term,TerminatorStep.after,LocalUnit.current,TerminatorStep.setControl,
      TerminatorStep.advanced,fields.1,fields.2.1,fields.2.2.1,fields.2.2.2.1,fields.2.2.2.2]
    all_goals exact ⟨trivial,trivial,trivial,trivial,trivial⟩
  · unfold Preservation.ExistingRoots at *
    dsimp only [final,ReturnContinuation.resume,FrameExit.afterRelevanceAt]
    split <;> simpa only [FrameExit.afterRelevance,term,TerminatorStep.after,LocalUnit.current,TerminatorStep.setControl] using roots
end EmptyFunction.LatentPreservation
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.LatentPreservation." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved latent preservation axiom {dependency} in {name}"
