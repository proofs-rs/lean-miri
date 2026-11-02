import duplicate_prefix.GeneralRangeMapThoroughEvery

namespace DuplicatePrefix.GeneralRangeMapThoroughComplete
open Miri Miri.ABI Miri.DataStructures
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapThoroughEvery
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private def Chain (start : UInt64) : List (RangeMapSegment α) → Prop
  | [] => True
  | row :: rest => row.range.start = start ∧ row.range.start < row.range.stop ∧ Chain row.range.stop rest

private def finish (start : UInt64) : List (RangeMapSegment α) → UInt64
  | [] => start
  | row :: rest => finish row.range.stop rest

private theorem chain_of_facts (items : List (RangeMapSegment α))
    (positive : ∀ i (h : i < items.length), items[i].range.start < items[i].range.stop)
    (adjacent : ∀ i (h : i+1 < items.length), items[i].range.stop = items[i+1].range.start) :
    ∀ start, (∀ h : 0 < items.length, items[0].range.start = start) → Chain start items := by
  induction items with
  | nil => intro start first;trivial
  | cons row rest ih =>
    intro start first
    refine ⟨first (by simp),positive 0 (by simp),?_⟩
    apply ih
    · intro i h;exact positive (i+1) (by simpa using Nat.succ_lt_succ h)
    · intro i h;exact adjacent (i+1) (by simpa [Nat.add_assoc] using Nat.succ_lt_succ h)
    · intro h;exact (adjacent 0 (by simpa using Nat.succ_lt_succ h)).symm

private theorem initial_chain (map : DedupRangeMap α) (well : map.WellFormed) : Chain 0 map.entries.toList := by
  by_cases empty : map.entries.size = 0
  · have none : map.entries = #[] := Array.size_eq_zero_iff.mp empty
    simp [none,Chain]
  · have facts : map.entries[0].range.start = 0 ∧
        (∀ i (h : i < map.entries.size), map.entries[i].range.start < map.entries[i].range.stop) ∧
        (∀ i (h : i+1 < map.entries.size), map.entries[i].range.stop = map.entries[i+1].range.start) := by
      simpa only [DedupRangeMap.WellFormed,empty,↓reduceDIte] using well
    apply chain_of_facts map.entries.toList
    · intro i h;simpa using facts.2.1 i (by simpa using h)
    · intro i h;simpa using facts.2.2 i (by simpa using h)
    · intro h;simpa using facts.1

private theorem push_well (entries : Array (RangeMapSegment α)) (row : RangeMapSegment α)
    (well : (⟨entries⟩ : DedupRangeMap α).WellFormed)
    (positive : row.range.start < row.range.stop)
    (boundary : match entries.back? with | none => row.range.start = 0 | some previous => previous.range.stop = row.range.start) :
    (⟨entries.push row⟩ : DedupRangeMap α).WellFormed := by
  have nonempty : (entries.push row).size ≠ 0 := by simp
  simp only [DedupRangeMap.WellFormed,nonempty,↓reduceDIte]
  by_cases empty : entries.size = 0
  · have none : entries = #[] := Array.size_eq_zero_iff.mp empty
    subst entries
    simp only [Array.back?_empty] at boundary
    refine ⟨by simpa using boundary,?_,?_⟩
    · intro i h
      have zero : i = 0 := by simpa using h
      subst i;simpa using positive
    · intro i h;simp at h
  · have facts : entries[0].range.start = 0 ∧
        (∀ i (h : i < entries.size), entries[i].range.start < entries[i].range.stop) ∧
        (∀ i (h : i+1 < entries.size), entries[i].range.stop = entries[i+1].range.start) := by
      simpa only [DedupRangeMap.WellFormed,empty,↓reduceDIte] using well
    refine ⟨?_,?_,?_⟩
    · simpa only [Array.getElem_push,show 0 < entries.size from by omega,↓reduceDIte] using facts.1
    · intro i h
      by_cases old : i < entries.size
      · simpa only [Array.getElem_push,old,↓reduceDIte] using facts.2.1 i old
      · have equal : i = entries.size := by simp only [Array.size_push] at h;omega
        subst i;simpa using positive
    · intro i h
      by_cases old : i+1 < entries.size
      · simpa only [Array.getElem_push,old,show i < entries.size from by omega,↓reduceDIte] using facts.2.2 i old
      · have equal : i+1 = entries.size := by simp only [Array.size_push] at h;omega
        have first : i < entries.size := by omega
        have back : entries.back? = some entries[i] := by
          rw [Array.back?_eq_getElem?,show entries.size-1 = i from by omega,Array.getElem?_eq_getElem first]
        rw [back] at boundary
        simpa only [Array.getElem_push,first,↓reduceDIte,show ¬i+1 < entries.size from by omega,↓reduceDIte] using boundary

private theorem extend_well (entries : Array (RangeMapSegment α)) (row : RangeMapSegment α)
    (nonempty : 0 < entries.size) (well : (⟨entries⟩ : DedupRangeMap α).WellFormed)
    (positive : row.range.start < row.range.stop)
    (boundary : entries[entries.size-1].range.stop = row.range.start) :
    (⟨entries.set (entries.size-1) {entries[entries.size-1] with range := {entries[entries.size-1].range with stop := row.range.stop}}⟩ : DedupRangeMap α).WellFormed := by
  have last : entries.size-1 < entries.size := by omega
  have old : entries.size ≠ 0 := by omega
  have facts : entries[0].range.start = 0 ∧
      (∀ i (h : i < entries.size), entries[i].range.start < entries[i].range.stop) ∧
      (∀ i (h : i+1 < entries.size), entries[i].range.stop = entries[i+1].range.start) := by
    simpa only [DedupRangeMap.WellFormed,old,↓reduceDIte] using well
  simp only [DedupRangeMap.WellFormed,Array.size_set,old,↓reduceDIte]
  refine ⟨?_,?_,?_⟩
  · by_cases same : entries.size-1 = 0 <;> simp [Array.getElem_set,same,facts.1]
  · intro i h
    by_cases same : entries.size-1 = i
    · subst i
      simp only [Array.getElem_set_self]
      have earlier := facts.2.1 (entries.size-1) last
      rw [boundary] at earlier
      exact UInt64.lt_iff_toNat_lt.mpr (by have a := UInt64.lt_iff_toNat_lt.mp earlier;have b := UInt64.lt_iff_toNat_lt.mp positive;omega)
    · simpa [Array.getElem_set,same] using facts.2.1 i h
  · intro i h
    have earlier : entries.size-1 ≠ i := by omega
    have left : ((entries.set (entries.size-1) {entries[entries.size-1] with range := {entries[entries.size-1].range with stop := row.range.stop}})[i]'(by simp only [Array.size_set];omega)).range.stop = entries[i].range.stop := by
      simp only [Array.getElem_set,earlier,↓reduceIte]
    have right : ((entries.set (entries.size-1) {entries[entries.size-1] with range := {entries[entries.size-1].range with stop := row.range.stop}})[i+1]'(by simp only [Array.size_set];omega)).range.start = entries[i+1].range.start := by
      by_cases same : entries.size-1 = i+1
      · simp only [Array.getElem_set,same,↓reduceIte]
      · simp only [Array.getElem_set,same,↓reduceIte]
    rw [left,right]
    exact facts.2.2 i h

private theorem finish_last (start : UInt64) (items : List (RangeMapSegment α)) :
    finish start items = (items.getLast?.map (fun row => row.range.stop)).getD start := by
  induction items generalizing start with
  | nil => rfl
  | cons row rest ih =>
    cases rest with
    | nil => rfl
    | cons next rest => simpa only [finish,List.getLast?_cons,Option.map_some,Option.getD_some] using ih row.range.stop

private theorem finish_size (map : DedupRangeMap α) : finish 0 map.entries.toList = map.size.bytes := by
  rw [finish_last]
  have back : map.entries.back? = map.entries.toList.getLast? := by
    simpa only [Array.toArray_toList] using List.back?_toArray map.entries.toList
  unfold DedupRangeMap.size
  rw [back]
  cases map.entries.toList.getLast? <;> rfl

/-- The real thorough merge on every well-formed partition succeeds and retains
well-formedness and byte capacity. No operation success is a premise. -/
theorem complete {α : Type} [DecidableEq α] (map : DedupRangeMap α) (well : map.WellFormed) :
    map.mergeAdjacentThorough.outcome = .ok () ∧
    map.mergeAdjacentThorough.state.WellFormed ∧ map.mergeAdjacentThorough.state.size = map.size := by
  have chain := initial_chain map well
  have endpoint := finish_size map
  unfold DedupRangeMap.mergeAdjacentThorough
  simp only [Id.run,bind,pure,←Array.forIn_toList]
  name_thorough_scan
  have go : ∀ (items : List (RangeMapSegment α)) (start : UInt64) (entries : Array (RangeMapSegment α)),
      Chain start items → (⟨entries⟩ : DedupRangeMap α).WellFormed →
      (⟨entries⟩ : DedupRangeMap α).size.bytes = start →
      (forIn items (none,entries) scan).1 = none ∧
      (⟨(forIn items (none,entries) scan).2⟩ : DedupRangeMap α).WellFormed ∧
      (⟨(forIn items (none,entries) scan).2⟩ : DedupRangeMap α).size.bytes = finish start items := by
    intro items
    induction items with
    | nil => intro start entries chain good size;exact ⟨rfl,good,size⟩
    | cons row rest ih =>
      intro start entries chain good size
      obtain ⟨rowStart,positive,tail⟩ := chain
      have pushed : (⟨entries.push row⟩ : DedupRangeMap α).size.bytes = row.range.stop := by
        simp only [DedupRangeMap.size,Array.back?_push,Size.ofBytes]
      cases back : entries.back? with
      | none =>
        have zero : start = 0 := by simpa only [DedupRangeMap.size,back,Size.ZERO] using size.symm
        have boundary : row.range.start = 0 := rowStart.trans zero
        have nextWell := push_well entries row good positive (by simpa only [back] using boundary)
        have actual : scan row (none,entries) = .yield (none,entries.push row) := by simp only [scan,back]
        have next := ih row.range.stop (entries.push row) tail nextWell pushed
        simpa only [List.forIn_cons,actual,bind,pure,finish] using next
      | some previous =>
        have boundary : previous.range.stop = row.range.start := by
          have endpoint : previous.range.stop = start := by simpa only [DedupRangeMap.size,back,Size.ofBytes] using size
          exact endpoint.trans rowStart.symm
        by_cases same : previous.data = row.data
        · have adjacent : (previous.range.stop != row.range.start) = false := by simp [boundary]
          have valid : entries.size-1 < entries.size := by
            obtain ⟨xs,rfl⟩ := Array.back?_eq_some_iff.mp back
            simp
          have previousAt : entries[entries.size-1] = previous := by
            have lookup : entries[entries.size-1]? = some previous := by rw [←Array.back?_eq_getElem?];exact back
            simpa only [Array.getElem?_eq_getElem valid,Option.some.injEq] using lookup
          let updated := entries.set (entries.size-1) {entries[entries.size-1] with range := {entries[entries.size-1].range with stop := row.range.stop}}
          have nextWell : (⟨updated⟩ : DedupRangeMap α).WellFormed :=
            extend_well entries row (by omega) good positive (by rw [previousAt];exact boundary)
          have nextSize : (⟨updated⟩ : DedupRangeMap α).size.bytes = row.range.stop := by
            unfold DedupRangeMap.size
            rw [Array.back?_eq_getElem?]
            simp only [updated,Array.size_set,Array.getElem?_set,ite_true]
            rfl
          have actual : scan row (none,entries) = .yield (none,updated) := by
            simp only [scan,back,same,↓reduceIte,adjacent,Bool.false_eq_true]
            simp_range_merge_source
            simp only [valid,↓reduceDIte,pure,Except.pure]
            rfl
          have next := ih row.range.stop updated tail nextWell nextSize
          simpa only [List.forIn_cons,actual,bind,pure,finish] using next
        · have nextWell := push_well entries row good positive (by simpa only [back] using boundary)
          have actual : scan row (none,entries) = .yield (none,entries.push row) := by simp only [scan,back,same,↓reduceIte]
          have next := ih row.range.stop (entries.push row) tail nextWell pushed
          simpa only [List.forIn_cons,actual,bind,pure,finish] using next
  have final := go map.entries.toList 0 #[] chain (by simp [DedupRangeMap.WellFormed]) rfl
  rw [final.1]
  refine ⟨rfl,final.2.1,?_⟩
  exact congrArg Size.mk (final.2.2.trans endpoint)

/-- Completion and geometry can be combined with any initially stored payload
invariant. Actual equal-run merging retains that invariant at every output row. -/
theorem complete_every {α : Type} [DecidableEq α] (predicate : α → Prop)
    (map : DedupRangeMap α) (well : map.WellFormed) (every : Every predicate map) :
    map.mergeAdjacentThorough.outcome = .ok () ∧
    map.mergeAdjacentThorough.state.WellFormed ∧ map.mergeAdjacentThorough.state.size = map.size ∧
    Every predicate map.mergeAdjacentThorough.state :=
  ⟨(complete map well).1,(complete map well).2.1,(complete map well).2.2,
    GeneralRangeMapThoroughEvery.preserves predicate map every⟩

end DuplicatePrefix.GeneralRangeMapThoroughComplete
