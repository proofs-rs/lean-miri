import duplicate_prefix.GeneralRangeMapThoroughEvery
import duplicate_prefix.GeneralRangeMapOrigins
namespace DuplicatePrefix.GeneralRangeMapThoroughOwnedOn
open Miri Miri.DataStructures
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapMerge DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem push_good {α : Type} (predicate : α → Prop) (lower upper : UInt64)
    (entries : Array (RangeMapSegment α)) (segment : RangeMapSegment α)
    (good : OwnedOn predicate lower upper ⟨entries⟩)
    (here : lower.toNat < upper.toNat → segment.range.start.toNat < upper.toNat → lower.toNat < segment.range.stop.toNat → predicate segment.data) :
    OwnedOn predicate lower upper ⟨entries.push segment⟩ := by
  intro i valid positive beforeUpper afterLower
  by_cases before : i < entries.size
  · have oldBefore : entries[i].range.start.toNat < upper.toNat := by simpa only [Array.getElem_push,before,↓reduceDIte] using beforeUpper
    have oldAfter : lower.toNat < entries[i].range.stop.toNat := by simpa only [Array.getElem_push,before,↓reduceDIte] using afterLower
    simpa only [Array.getElem_push,before,↓reduceDIte] using good i before positive oldBefore oldAfter
  · have equal : i = entries.size := by simp only [Array.size_push] at valid;omega
    subst i
    simp only [Array.getElem_push_eq] at beforeUpper afterLower ⊢
    exact here positive beforeUpper afterLower

private theorem extend_good {α : Type} (predicate : α → Prop) (lower upper : UInt64)
    (entries : Array (RangeMapSegment α)) (i : Nat) (valid : i < entries.size)
    (segment : RangeMapSegment α) (good : OwnedOn predicate lower upper ⟨entries⟩)
    (here : lower.toNat < upper.toNat → segment.range.start.toNat < upper.toNat → lower.toNat < segment.range.stop.toNat → predicate segment.data)
    (touching : entries[i].range.stop = segment.range.start) (sameData : entries[i].data = segment.data) :
    OwnedOn predicate lower upper ⟨entries.set i {entries[i] with range := {entries[i].range with stop := segment.range.stop}}⟩ := by
  intro q bounded positive beforeUpper afterLower
  have oldBound : q < entries.size := by simpa only [Array.size_set] using bounded
  by_cases equal : i = q
  · subst q
    simp only [Array.getElem_set_self] at beforeUpper afterLower ⊢
    by_cases oldAfter : lower.toNat < entries[i].range.stop.toNat
    · exact good i valid positive beforeUpper oldAfter
    · rw [sameData]
      exact here positive (by rw [←touching];omega) afterLower
  · have oldBefore : entries[q].range.start.toNat < upper.toNat := by simpa [Array.getElem_set,equal,Ne.symm equal] using beforeUpper
    have oldAfter : lower.toNat < entries[q].range.stop.toNat := by simpa [Array.getElem_set,equal,Ne.symm equal] using afterLower
    simpa [Array.getElem_set,equal,Ne.symm equal] using good q oldBound positive oldBefore oldAfter

theorem preserves {α : Type} [DecidableEq α] (predicate : α → Prop) (lower upper : UInt64) (map : DedupRangeMap α)
    (good : OwnedOn predicate lower upper map) : OwnedOn predicate lower upper map.mergeAdjacentThorough.state := by
  unfold DedupRangeMap.mergeAdjacentThorough
  simp only [Id.run,bind,pure,←Array.forIn_toList]
  name_thorough_scan
  let property := fun state : Option (DedupMutationResult (DedupRangeMap α)) × Array (RangeMapSegment α) =>
    OwnedOn predicate lower upper ⟨state.2⟩ ∧ ∀ result, state.1 = some result → OwnedOn predicate lower upper result.state
  have step : ∀ segment ∈ map.entries.toList, ∀ state, property state → property (scan segment state).value := by
    intro segment member state preserved
    have here : ∀ positive : lower.toNat < upper.toNat, segment.range.start.toNat < upper.toNat → lower.toNat < segment.range.stop.toNat → predicate segment.data := by
      intro positive before after
      have arrayMember : segment ∈ map.entries := by simpa using member
      obtain ⟨i,valid,equal⟩ := Array.mem_iff_getElem.mp arrayMember
      rw [←equal] at before after ⊢
      exact good i valid positive before after
    rcases state with ⟨returned,entries⟩
    rcases preserved with ⟨all,_⟩
    have yielded : property (none,entries.push segment) := ⟨push_good predicate lower upper entries segment all here,by simp⟩
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
          have last : entries[entries.size-1] = previous := by
            have exactBack := Array.getElem?_eq_getElem valid
            rw [←Array.back?_eq_getElem?,back] at exactBack
            exact Option.some.inj exactBack.symm
          have touching : entries[entries.size-1].range.stop = segment.range.start := by
            rw [last]
            simpa only [bne_eq_false_iff_eq] using adjacent
          have sameData : entries[entries.size-1].data = segment.data := by rw [last];exact equalData
          exact ⟨extend_good predicate lower upper entries _ valid segment all here touching sameData,by simp⟩
      · simpa only [scan,back,equalData,↓reduceIte,ForInStep.value] using yielded
  have initial : property (none,#[]) := ⟨by intro i valid;simpa using valid,by simp⟩
  have final := GeneralBorrowLoop.list_invariant map.entries.toList scan property step (none,#[]) initial
  cases returned : (forIn map.entries.toList (none,#[]) scan).1 with
  | none => exact final.1
  | some result => exact final.2 result returned
end DuplicatePrefix.GeneralRangeMapThoroughOwnedOn
