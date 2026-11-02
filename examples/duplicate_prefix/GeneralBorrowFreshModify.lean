import duplicate_prefix.GeneralBorrowFreshRange
namespace DuplicatePrefix.GeneralBorrowFreshModify
open Miri.ABI Miri.DataStructures
open DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- A total array-position update, used only to describe the real modifier's
successful data result. Out-of-bounds positions retain the map. -/
def atPosition (map : DedupRangeMap α) (position : Nat) (modify : ByteRange → α → α) : DedupRangeMap α :=
  if valid : position < map.entries.size then
    let old := map.entries[position]
    ⟨map.entries.set position {old with data := modify old.range old.data} valid⟩
  else map

theorem atPosition_size (map : DedupRangeMap α) (position : Nat) (modify : ByteRange → α → α) :
    (atPosition map position modify).entries.size = map.entries.size := by
  unfold atPosition
  split <;> simp

theorem atPosition_get (map : DedupRangeMap α) (position query : Nat)
    (modify : ByteRange → α → α) (valid : query < map.entries.size) :
    (atPosition map position modify).entries[query]'(by rw [atPosition_size];exact valid) =
      if position = query then {map.entries[query] with data := modify map.entries[query].range map.entries[query].data}
      else map.entries[query] := by
  unfold atPosition
  split
  · simp only [Array.getElem_set]
    by_cases same : position = query
    · subst position;simp
    · simp only [same,↓reduceIte]
  · rename_i outside
    have different : position ≠ query := by intro same;subst position;exact outside valid
    simp only [different,↓reduceIte]

theorem fold_size (map : DedupRangeMap α) (positions : List Nat) (modify : ByteRange → α → α) :
    (positions.foldl (fun current position => atPosition current position modify) map).entries.size = map.entries.size := by
  induction positions generalizing map with
  | nil => rfl
  | cons position rest ih => simpa only [List.foldl_cons,atPosition_size] using ih (atPosition map position modify)

/-- With an idempotent callback, every selected position contains exactly its
modified original data, even if a position were repeated in the iterator. -/
theorem fold_get (positions : List Nat) (modify : ByteRange → α → α)
    (idempotent : ∀ range value, modify range (modify range value) = modify range value)
    (map : DedupRangeMap α) (query : Nat) (valid : query < map.entries.size) :
    (positions.foldl (fun current position => atPosition current position modify) map).entries[query]'(by rw [fold_size];exact valid) =
      if query ∈ positions then {map.entries[query] with data := modify map.entries[query].range map.entries[query].data}
      else map.entries[query] := by
  induction positions generalizing map with
  | nil => simp
  | cons position rest ih =>
    have nextValid : query < (atPosition map position modify).entries.size := by rw [atPosition_size];exact valid
    have next := ih (atPosition map position modify) nextValid
    rw [atPosition_get map position query modify valid] at next
    by_cases same : position = query
    · subst position
      by_cases member : query ∈ rest
      · simpa [member,idempotent] using next
      · simpa [member] using next
    · simpa only [List.foldl_cons,List.mem_cons,Ne.symm same,false_or,same,↓reduceIte] using next

/-- The actual modifier state is exactly the fold of its prepared position
updates. Preparation and all in-loop bounds are derived from the original
well-formedness and request bounds. -/
theorem state_exact {α : Type} [DecidableEq α] (map : DedupRangeMap α)
    (offset len : Size) (modify : ByteRange → α → α) (well : map.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat) :
    (map.modifyRange offset len modify).state =
      (map.iterMut offset len).positions.toList.foldl
        (fun current position => atPosition current position modify) (map.iterMut offset len).state := by
  let prepared := map.iterMutWithClone offset len id
  have preparedGood := GeneralRangeMapSafety.iter_mut_with_clone (fun _ : α => True)
    map offset len id well (fun _ _ => trivial) (fun _ _ => trivial) bounds
  unfold DedupRangeMap.modifyRange DedupRangeMap.modifyRangeWithClone
  simp only [Id.run,bind,pure,preparedGood.outcome,←Array.forIn_toList]
  name_fresh_modify_scan
  have scans : ∀ items : List Nat, (∀ position ∈ items, position < prepared.state.entries.size) →
      ∀ (current : DedupRangeMap α) (segments : Array (RangeMapSegment α)),
        current.entries.size = prepared.state.entries.size →
        (forIn items (none,current,segments) scan).1 = none ∧
        (forIn items (none,current,segments) scan).2.1 =
          items.foldl (fun current position => atPosition current position modify) current := by
    intro items
    induction items with
    | nil => intro _ current segments _; constructor <;> rfl
    | cons position rest ih =>
      intro bounded current segments sizeEq
      have valid : position < current.entries.size := by rw [sizeEq];exact bounded position (by simp)
      let updated : RangeMapSegment α := {current.entries[position]'valid with
        data := modify (current.entries[position]'valid).range (current.entries[position]'valid).data}
      let next : DedupRangeMap α := ⟨current.entries.set position updated valid⟩
      have actual : scan position (none,current,segments) = .yield (none,next,segments.push updated) := by
        simp only [scan]
        unfold_range_update_source
        simp only [valid,↓reduceDIte,Except.pure,pure]
        rfl
      have nextSize : next.entries.size = prepared.state.entries.size := by
        simpa only [next,Array.size_set] using sizeEq
      have continued := ih (fun other member => bounded other (by simp [member])) next (segments.push updated) nextSize
      simpa only [List.forIn_cons,actual,bind,List.foldl_cons,atPosition,valid,↓reduceDIte,next,updated] using continued
  have bounded : ∀ position ∈ prepared.positions.toList, position < prepared.state.entries.size := by
    intro position member
    obtain ⟨cursor,valid,equal⟩ := Array.mem_iff_getElem.mp (Array.mem_def.mpr member)
    have known := (preparedGood.selected cursor valid).choose
    rw [equal] at known
    exact known
  have result := scans prepared.positions.toList bounded prepared.state #[] rfl
  rw [result.1]
  exact result.2
end DuplicatePrefix.GeneralBorrowFreshModify
#print axioms DuplicatePrefix.GeneralBorrowFreshModify.state_exact
namespace DuplicatePrefix.GeneralBorrowFreshModify
open Miri.ABI Miri.DataStructures

/-- Exact data at each actual modifier output slot for idempotent callbacks.
The branch test refers to the real iterator's selected position list. -/
theorem entry_exact {α : Type} [DecidableEq α] (map : DedupRangeMap α)
    (offset len : Size) (modify : ByteRange → α → α)
    (idempotent : ∀ range value, modify range (modify range value) = modify range value)
    (well : map.WellFormed) (bounds : offset.bytes.toNat+len.bytes.toNat ≤ map.size.bytes.toNat)
    (query : Nat) (valid : query < (map.iterMut offset len).state.entries.size) :
    ∃ outputValid : query < (map.modifyRange offset len modify).state.entries.size,
      (map.modifyRange offset len modify).state.entries[query]'outputValid =
        if query ∈ (map.iterMut offset len).positions.toList then
          {(map.iterMut offset len).state.entries[query] with
            data := modify (map.iterMut offset len).state.entries[query].range
              (map.iterMut offset len).state.entries[query].data}
        else (map.iterMut offset len).state.entries[query] := by
  have exactState := state_exact map offset len modify well bounds
  have sizeEq : (map.modifyRange offset len modify).state.entries.size = (map.iterMut offset len).state.entries.size := by
    rw [exactState,fold_size]
  refine ⟨by rw [sizeEq];exact valid,?_⟩
  simpa only [exactState] using fold_get (map.iterMut offset len).positions.toList modify idempotent
    (map.iterMut offset len).state query valid
end DuplicatePrefix.GeneralBorrowFreshModify
#print axioms DuplicatePrefix.GeneralBorrowFreshModify.entry_exact
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshModify." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual range modification dependency {dependency}"
