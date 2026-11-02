import duplicate_prefix.GeneralRangeMapThoroughEvery
import duplicate_prefix.GeneralRangeMapOrigins
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingActivityMerge
open Miri Miri.ABI Miri.DataStructures
open GeneralRangeMapOrigins GeneralRangeMapState GeneralRangeMapMerge RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem push_good {α : Type} (original : DedupRangeMap α) (entries : Array (RangeMapSegment α)) (segment : RangeMapSegment α)
    (good : Refines original ⟨entries⟩)
    (here : ∀ point,segment.range.start.toNat ≤ point.toNat → point.toNat < segment.range.stop.toNat → ValueAt original point segment.data) :
    Refines original ⟨entries.push segment⟩ := by
  intro point value atPoint
  obtain ⟨index,valid,lower,upper,equal⟩ := atPoint
  by_cases before : index < entries.size
  · exact good point value ⟨index,before,by simpa only [Array.getElem_push,before,↓reduceDIte] using lower,
      by simpa only [Array.getElem_push,before,↓reduceDIte] using upper,by simpa only [Array.getElem_push,before,↓reduceDIte] using equal⟩
  · have same : index = entries.size := by simp only [Array.size_push] at valid;omega
    subst index
    simp only [Array.getElem_push_eq] at lower upper equal
    rw [←equal]
    exact here point lower upper

private theorem extend_good {α : Type} (original : DedupRangeMap α) (entries : Array (RangeMapSegment α))
    (index : Nat) (valid : index < entries.size) (segment : RangeMapSegment α)
    (good : Refines original ⟨entries⟩)
    (here : ∀ point,segment.range.start.toNat ≤ point.toNat → point.toNat < segment.range.stop.toNat → ValueAt original point segment.data)
    (touching : entries[index].range.stop = segment.range.start) (sameData : entries[index].data = segment.data) :
    Refines original ⟨entries.set index {entries[index] with range := {entries[index].range with stop := segment.range.stop}}⟩ := by
  intro point value atPoint
  obtain ⟨query,bounded,lower,upper,equal⟩ := atPoint
  have oldBound : query < entries.size := by simpa only [Array.size_set] using bounded
  by_cases same : index = query
  · subst query
    simp only [Array.getElem_set_self] at lower upper equal
    by_cases before : point.toNat < entries[index].range.stop.toNat
    · exact good point value ⟨index,valid,lower,before,equal⟩
    · rw [←equal,sameData]
      exact here point (by rw [←touching];omega) upper
  · exact good point value ⟨query,oldBound,by simpa [Array.getElem_set,same,Ne.symm same] using lower,
      by simpa [Array.getElem_set,same,Ne.symm same] using upper,by simpa [Array.getElem_set,same,Ne.symm same] using equal⟩

/-- Every byte/value in the real thorough merge has a byte/value witness before
merging, including returned partial error prefixes. -/
theorem refines {α : Type} [DecidableEq α] (map : DedupRangeMap α) : Refines map map.mergeAdjacentThorough.state := by
  unfold DedupRangeMap.mergeAdjacentThorough
  simp only [Id.run,bind,pure,←Array.forIn_toList]
  name_thorough_scan
  let property := fun state : Option (DedupMutationResult (DedupRangeMap α)) × Array (RangeMapSegment α) =>
    Refines map ⟨state.2⟩ ∧ ∀ result,state.1 = some result → Refines map result.state
  have step : ∀ segment ∈ map.entries.toList,∀ state,property state → property (scan segment state).value := by
    intro segment member state preserved
    have here : ∀ point,segment.range.start.toNat ≤ point.toNat → point.toNat < segment.range.stop.toNat → ValueAt map point segment.data := by
      intro point lower upper
      obtain ⟨index,valid,equal⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp member)
      exact ⟨index,valid,by rw [equal];exact lower,by rw [equal];exact upper,by rw [equal]⟩
    rcases state with ⟨returned,entries⟩
    rcases preserved with ⟨all,_⟩
    have yielded : property (none,entries.push segment) := ⟨push_good map entries segment all here,by simp⟩
    have failed : ∀ outcome,property (some {state := ⟨entries⟩,outcome := outcome},entries) := by
      intro outcome;exact ⟨all,fun result equal => by cases equal;exact all⟩
    cases back : entries.back? with
    | none => simpa only [scan,back,ForInStep.value] using yielded
    | some previous =>
      by_cases equalData : previous.data = segment.data
      · cases adjacent : (previous.range.stop != segment.range.start) with
        | true => simpa only [scan,back,equalData,↓reduceIte,adjacent,ForInStep.value] using failed (.error (.mergeRequiresAdjacent previous.range.stop segment.range.start))
        | false =>
          have valid : entries.size-1 < entries.size := by obtain ⟨rest,equal⟩ := Array.back?_eq_some_iff.mp back;rw [equal];simp
          simp only [scan,back,equalData,↓reduceIte,adjacent,Bool.false_eq_true]
          simp_range_merge_source
          simp only [valid,↓reduceDIte,↓reduceIte,pure,Except.pure,bind,Except.bind,ForInStep.value]
          have last : entries[entries.size-1] = previous := by
            have exactBack := Array.getElem?_eq_getElem valid
            rw [←Array.back?_eq_getElem?,back] at exactBack
            exact Option.some.inj exactBack.symm
          have touching : entries[entries.size-1].range.stop = segment.range.start := by rw [last];simpa only [bne_eq_false_iff_eq] using adjacent
          have sameData : entries[entries.size-1].data = segment.data := by rw [last];exact equalData
          exact ⟨extend_good map entries _ valid segment all here touching sameData,by simp⟩
      · simpa only [scan,back,equalData,↓reduceIte,ForInStep.value] using yielded
  have initial : property (none,#[]) := ⟨by intro point value ⟨index,valid,_,_,_⟩;simpa using valid,by simp⟩
  have final := GeneralBorrowLoop.list_invariant map.entries.toList scan property step (none,#[]) initial
  cases returned : (forIn map.entries.toList (none,#[]) scan).1 with
  | none => exact final.1
  | some result => exact final.2 result returned
end DuplicatePrefix.GeneralBorrowProtectedSiblingActivityMerge
