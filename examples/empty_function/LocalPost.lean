import empty_function.LocalModel
import empty_function.TerminatorStep
import empty_function.FrameExit

/-! Thread projections of the computed integer-destination call poststate. -/
namespace EmptyFunction.LocalPost
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

 theorem projections (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) (index : Nat)
    (after : WholeCall.State) (computed : after.machine = LocalModel.machine s p tracker destination older bound frame previous index) :
    Preservation.OtherThreads p.before after ∧ Preservation.ThreadContext p.before after := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold Preservation.OtherThreads Preservation.ThreadContext
  rw [computed]
  unfold LocalModel.machine LocalModel.initializedMachine
  rw [fields.freshLocalsIdentity]
  by_cases pushed : frame.extra.userRelevance >= previous.extra.userRelevance <;>
    by_cases popped : index = (older.push (LocalModel.caller s p tracker destination bound)).size <;>
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





 theorem fields (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) (index : Nat) :
    (LocalModel.machine s p tracker destination older bound frame previous index).memory = p.before.machine.memory ∧
    (LocalModel.machine s p tracker destination older bound frame previous index).user.addresses = p.before.machine.user.addresses ∧
    (LocalModel.machine s p tracker destination older bound frame previous index).borrowTracker = p.before.machine.borrowTracker ∧
    Preservation.RuntimeContext p.before (⟨p.before.stack,LocalModel.machine s p tracker destination older bound frame previous index⟩ : State) := by
  have fields := MetadataBinding.fields s metadata capacity
  unfold LocalModel.machine LocalModel.initializedMachine
  rw [fields.freshLocalsIdentity]
  by_cases pushed : frame.extra.userRelevance >= previous.extra.userRelevance <;>
    by_cases popped : index = (older.push (LocalModel.caller s p tracker destination bound)).size <;>
    simp only [FrameExit.afterRelevanceAt,popped,FrameExit.afterRelevance,
      FrameRelevance.pushedMachine,pushed,TerminatorStep.after,LocalUnit.current,
      ↓reduceIte,Preservation.RuntimeContext]
  all_goals repeat' constructor

private theorem old_rights_refl (tree : Miri.TreeBorrows.BorrowTree) : Preservation.OldNodeRights tree tree := by
  refine ⟨?_,?_,?_⟩
  · intro tag index found; exact found
  · intro root member; exact member
  · intro index old found
    refine ⟨old,found,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
    · intro child member; exact member
    · intro byte segment member contains; exact ⟨segment,member,contains,rfl,rfl⟩

 theorem preserves (s : Static) (metadata : Metadata s) (capacity : 0 < s.capacity)
    (p : Packet) (tracker : MachineHooks.BorrowState)
    (destination : InputDraft.LocalDestination s p tracker) (older : Array LocalUnit.F)
    (bound : destination.localId < destination.caller.locals.size) (frame previous : LocalUnit.F) (index : Nat)
    (original : p.before.stack.frames = older.push destination.caller)
    (whole : destination.offset = none) :
    Preservation.Preserves s p (LocalModel.finish s p tracker destination older bound frame previous index) := by
  let finish := LocalModel.finish s p tracker destination older bound frame previous index
  have field := fields s metadata capacity p tracker destination older bound frame previous index
  have threads := projections s metadata capacity p tracker destination older bound frame previous index finish rfl
  refine ⟨?_,?_,?_,threads.1,?_,?_,?_,threads.2,?_,field.2.2.2,?_⟩
  · simp [Returned,LocalModel.finish,ReturnContinuation.resume,original,Stack.currentFrame?,LocalModel.caller,LocalImmediate.cached]
  · intro id old found
    refine ⟨old,?_,rfl,rfl,old_rights_refl _⟩
    change (LocalModel.machine s p tracker destination older bound frame previous index).memory.live.find? (fun row => row.1 == id) = _
    rw [field.1]; exact found
  · intro old found
    exact ⟨old,field.2.2.1.trans found,rfl⟩
  · intro old current oldEq currentEq
    simp only [Stack.currentFrame?,original,LocalModel.finish,ReturnContinuation.resume,Array.back?_push,Option.some.injEq] at oldEq currentEq
    subst old; subst current
    refine ⟨by simp [LocalModel.caller,LocalImmediate.cached],?_⟩
    intro slot permitted
    rw [destination.encoding] at permitted
    simp only at permitted
    simp [LocalModel.caller,LocalImmediate.cached,Array.getElem?_set,permitted,Ne.symm permitted]
  · simp [Preservation.SelectedProjectedContents,destination.encoding,whole]
  · intro old current oldEq currentEq
    simp only [Stack.currentFrame?,original,LocalModel.finish,ReturnContinuation.resume,Array.back?_push,Option.some.injEq] at oldEq currentEq
    subst old; subst current
    rfl
  · unfold Preservation.ExistingAddressFacts
    dsimp only [LocalModel.finish,ReturnContinuation.resume]
    rw [field.2.1]
    refine ⟨rfl,rfl,?_,?_,?_⟩
    · intro id row found; exact found
    · intro row member; exact ⟨row,member,rfl,rfl⟩
    · intro id member; exact Array.contains_iff_mem.mpr member
  · intro old found
    refine ⟨old,field.2.2.1.trans found,?_⟩
    intro id tag found; exact found

end EmptyFunction.LocalPost

open Lean Elab Command in
run_cmd do
  let mut count : Nat := 0
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "EmptyFunction.LocalPost.").length != 1 then
      count := count+1
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved local-post axiom: {name}: {dependency}"
  logInfo m!"Audited {count} local-post declarations"
