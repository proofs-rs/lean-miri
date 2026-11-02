import empty_function.CanonicalInit
import empty_function.TerminatorStep
import empty_function.FrameExit

/-! Thread projections of the computed integer-destination call poststate. -/
namespace EmptyFunction.IntegerThreads
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.Concurrency
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
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
  | some thread =>
    by_cases same : index = active <;> simp [same]

private theorem other_cache (threads : List ThreadRecord) (active : Nat) (cache : Option Nat)
    (index : Nat) (different : index ≠ active) :
    (threads.mapIdx (fun i thread => if i == active then
      {thread with topUserRelevantFrame := cache} else thread))[index]? = threads[index]? := by
  simp [List.getElem?_mapIdx,different]

def machine (s : Static) (p : Packet) (frame previous : LocalUnit.F)
    (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (index : Nat) :=
  FrameExit.afterRelevanceAt p.before.stack.frames frame
    ((TerminatorStep.after (LocalUnit.current p.before.stack.frames frame
      (CanonicalInit.initializedMachine s p frame previous tracker room))).machine) index

 theorem projections (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (frame previous : LocalUnit.F) (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) (index : Nat)
    (after : WholeCall.State) (computed : after.machine = machine s p frame previous tracker room index) :
    Preservation.OtherThreads p.before after ∧ Preservation.ThreadContext p.before after := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold Preservation.OtherThreads Preservation.ThreadContext
  rw [computed]
  unfold machine CanonicalInit.initializedMachine UnitRetag.allocatedMachine
  rw [fields.freshLocalsIdentity]
  by_cases pushed : frame.extra.userRelevance >= previous.extra.userRelevance <;>
    by_cases popped : index = p.before.stack.frames.size <;>
    simp only [FrameExit.afterRelevanceAt,popped,FrameExit.afterRelevance,
      FrameRelevance.pushedMachine,pushed,TerminatorStep.after,LocalUnit.current,
      ↓reduceIte,Preservation.eraseThreadRelevance]
  all_goals
    constructor
    · refine ⟨True.intro,?_,?_⟩
      · simp
      · intro i different
        simp only [other_cache _ _ _ i different]
    · simp only [erase_cache]

end EmptyFunction.IntegerThreads
