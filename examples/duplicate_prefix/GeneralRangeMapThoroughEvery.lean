import duplicate_prefix.GeneralRangeMapMerge
import duplicate_prefix.GeneralBorrowLoop
namespace DuplicatePrefix.GeneralRangeMapThoroughEvery
open Miri.DataStructures
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapMerge DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

open Lean Elab Tactic in
elab "name_thorough_scan" : tactic => do
  liftMetaTactic fun goal => goal.withContext do
    let target ← goal.getType
    let some loop := target.find? (fun expr => expr.isAppOf ``ForIn.forIn)
      | throwError "no actual thorough merge loop"
    let body := loop.getAppArgs.back!
    let goal ← goal.define `scan (←Lean.Meta.inferType body) body
    let (scan,goal) ← goal.intro1P
    return [←goal.change (target.replace fun expr => if expr == body then some (mkFVar scan) else none)]

private theorem push_good {α : Type} (predicate : α → Prop) (entries : Array (RangeMapSegment α))
    (segment : RangeMapSegment α) (good : Every predicate ⟨entries⟩) (here : predicate segment.data) :
    Every predicate ⟨entries.push segment⟩ := by
  intro i valid
  by_cases before : i < entries.size
  · simpa only [Array.getElem_push,before,↓reduceDIte] using good i before
  · have equal : i = entries.size := by simp only [Array.size_push] at valid;omega
    subst i
    simpa using here

private theorem extend_good {α : Type} (predicate : α → Prop) (entries : Array (RangeMapSegment α))
    (i : Nat) (valid : i < entries.size) (stop : UInt64) (good : Every predicate ⟨entries⟩) :
    Every predicate ⟨entries.set i {entries[i] with range := {entries[i].range with stop := stop}}⟩ := by
  intro q bounded
  have oldBound : q < entries.size := by simpa only [Array.size_set] using bounded
  by_cases equal : i = q
  · subst q
    simpa only [Array.getElem_set_self] using good i valid
  · simpa [Array.getElem_set,equal,Ne.symm equal] using good q oldBound

theorem preserves {α : Type} [DecidableEq α] (predicate : α → Prop) (map : DedupRangeMap α)
    (good : Every predicate map) : Every predicate map.mergeAdjacentThorough.state := by
  unfold DedupRangeMap.mergeAdjacentThorough
  simp only [Id.run,bind,pure,←Array.forIn_toList]
  name_thorough_scan
  let property := fun state : Option (DedupMutationResult (DedupRangeMap α)) × Array (RangeMapSegment α) =>
    Every predicate ⟨state.2⟩ ∧ ∀ result, state.1 = some result → Every predicate result.state
  have step : ∀ segment ∈ map.entries.toList, ∀ state, property state → property (scan segment state).value := by
    intro segment member state preserved
    have here : predicate segment.data := by
      have arrayMember : segment ∈ map.entries := by simpa using member
      obtain ⟨i,valid,equal⟩ := Array.mem_iff_getElem.mp arrayMember
      rw [←equal]
      exact good i valid
    rcases state with ⟨returned,entries⟩
    rcases preserved with ⟨all,_⟩
    have yielded : property (none,entries.push segment) := ⟨push_good predicate entries segment all here,by simp⟩
    have failed : ∀ outcome, property (some {state := ⟨entries⟩,outcome := outcome},entries) := by
      intro outcome
      exact ⟨all,fun result equal => by cases equal;exact all⟩
    cases back : entries.back? with
    | none => simpa only [scan,back,ForInStep.value] using yielded
    | some previous =>
      by_cases equalData : previous.data = segment.data
      · cases adjacent : (previous.range.stop != segment.range.start) with
        | true => simpa only [scan,back,equalData,↓reduceIte,adjacent,ForInStep.value] using
            failed (.error (.mergeRequiresAdjacent previous.range.stop segment.range.start))
        | false =>
          have valid : entries.size-1 < entries.size := by
            obtain ⟨rest,equal⟩ := Array.back?_eq_some_iff.mp back
            rw [equal]
            simp
          simp only [scan,back,equalData,↓reduceIte,adjacent,Bool.false_eq_true]
          simp_range_merge_source
          simp only [valid,↓reduceDIte,↓reduceIte,pure,Except.pure,bind,Except.bind,ForInStep.value]
          exact ⟨extend_good predicate entries _ valid segment.range.stop all,by simp⟩
      · simpa only [scan,back,equalData,↓reduceIte,ForInStep.value] using yielded
  have initial : property (none,#[]) := ⟨by intro i valid;simpa using valid,by simp⟩
  have final := GeneralBorrowLoop.list_invariant map.entries.toList scan property step (none,#[]) initial
  cases returned : (forIn map.entries.toList (none,#[]) scan).1 with
  | none => exact final.1
  | some result => exact final.2 result returned
end DuplicatePrefix.GeneralRangeMapThoroughEvery
