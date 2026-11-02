import duplicate_prefix.GeneralBorrowConcreteRangeInvariant

namespace DuplicatePrefix.S02DisjointReadFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralRangeMapState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Replacing an iterator-selected segment cannot affect an owned predicate
on a disjoint window, regardless of the access result. -/
private theorem replaced_outside {α : Type} (predicate : α → Prop)
    (map : DedupRangeMap α) (position : Nat) (valid : position < map.entries.size)
    (data : α) (lower upper : UInt64)
    (owned : OwnedOn predicate lower upper map)
    (outside : map.entries[position].range.stop.toNat ≤ lower.toNat ∨
      upper.toNat ≤ map.entries[position].range.start.toNat) :
    OwnedOn predicate lower upper (replaced map position valid data) := by
  intro query bounded positive beforeUpper afterLower
  have oldBound : query < map.entries.size := by
    simpa only [replaced_length] using bounded
  rw [replaced_range map position valid data query oldBound] at beforeUpper afterLower
  have different : position ≠ query := by
    intro same
    subst query
    rcases outside with left | right <;> omega
  simpa only [replaced,Array.getElem_set, different,↓reduceIte] using
    owned query oldBound positive beforeUpper afterLower

/-- The actual concrete Read modifies selected source segments only. An
arbitrary property of rows intersecting a disjoint destination window is
preserved even when the access fails. -/
theorem concrete (tree : BorrowTree) (tag : BorTag) (anchor : UniIndex)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (offset len : Size) (kind : AccessKind) (protections : ProtectedTags)
    (mode : ChildrenVisitMode) (predicate : LocationTree → Prop)
    (lower upper : UInt64)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (outside : offset.bytes.toNat + len.bytes.toNat ≤ lower.toNat ∨
      upper.toNat ≤ offset.bytes.toNat)
    (owned : OwnedOn predicate lower upper tree.locations) :
    OwnedOn predicate lower upper
      (tree.performBorrowAccessRange (.concrete tag) offset len kind protections mode).tree.locations := by
  let prepared := tree.locations.iterMut offset len
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have good := preparedData.1
  have preparedOwned := refines_owned_on tree.locations prepared.state predicate lower upper
    preparedData.1.wellFormed preparedData.2.1 owned
  unfold BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,good.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree ×
      Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.1.entries.map (·.range) = prepared.state.entries.map (·.range) ∧
      OwnedOn predicate lower upper state.1
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state maintained
    rcases state with ⟨current,visited,status⟩
    rcases maintained with ⟨ranges,currentOwned⟩
    by_cases completed : status = .Completed
    · subst status
      have sizeEq : current.entries.size = prepared.state.entries.size := by
        have known := congrArg Array.size ranges
        simpa only [Array.size_map] using known
      have cursorBound : cursor < prepared.positions.size := by
        have := List.mem_range'_1.mp member
        omega
      have segmentBound : cursor < prepared.segments.size := by
        rw [←good.lengths]
        exact cursorBound
      let position := prepared.positions[cursor]'cursorBound
      let segment := prepared.segments[cursor]'segmentBound
      obtain ⟨positionBound,selected⟩ := good.selected cursor cursorBound
      have currentBound : position < current.entries.size := by
        rw [sizeEq]
        exact positionBound
      have rangeSame : current.entries[position].range = segment.range := by
        have known := congrArg (fun rows => rows[position]?) ranges
        simp only [Array.getElem?_map,
          Array.getElem?_eq_getElem (xs := current.entries) (i := position) currentBound,
          Array.getElem?_eq_getElem (xs := prepared.state.entries) (i := position) positionBound,
          Option.map_some,Option.some.injEq] at known
        have selectedRange : prepared.state.entries[position].range = segment.range :=
          (congrArg (fun entry : RangeMapSegment LocationTree => entry.range) selected).symm
        exact known.trans selectedRange
      have selectedWithin := preparedData.2.2 cursor segmentBound
      change offset.bytes.toNat ≤ segment.range.start.toNat ∧
        segment.range.stop.toNat ≤ (offset.bytes+len.bytes).toNat at selectedWithin
      have fits : offset.bytes.toNat + len.bytes.toNat < 2^64 :=
        Nat.lt_of_le_of_lt bounds tree.locations.size.bytes.toNat_lt
      have stopEq : (offset.bytes+len.bytes).toNat = offset.bytes.toNat+len.bytes.toNat := by
        rw [UInt64.toNat_add,Nat.mod_eq_of_lt fits]
      have selectedOutside : current.entries[position].range.stop.toNat ≤ lower.toNat ∨
          upper.toNat ≤ current.entries[position].range.start.toNat := by
        rw [rangeSame]
        rw [stopEq] at selectedWithin
        rcases outside with left | right
        · exact Or.inl (by omega)
        · exact Or.inr (by omega)
      let access := source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range
      let mutation := current.setAtPos position (source_access_location access)
      have afterRanges : mutation.state.entries.map (·.range) = prepared.state.entries.map (·.range) := by
        dsimp only [mutation]
        rw [setAtPos_exact current position currentBound,replaced_ranges]
        exact ranges
      have afterOwned : OwnedOn predicate lower upper mutation.state := by
        dsimp only [mutation]
        rw [setAtPos_exact current position currentBound]
        exact replaced_outside predicate current position currentBound _ lower upper currentOwned selectedOutside
      have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position :=
        Array.getElem?_eq_getElem cursorBound
      have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment :=
        Array.getElem?_eq_getElem segmentBound
      dsimp only [mutation,access] at afterRanges afterOwned
      cases failure : source_access_status access
      all_goals dsimp only [access] at failure
      all_goals simpa only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
        setAtPos_success current position currentBound,failure,property,ForInStep.value]
        using And.intro afterRanges afterOwned
    · simpa only [scan,beq_iff_eq,completed,Bool.false_eq_true,↓reduceIte,
        ForInStep.value,property] using And.intro ranges currentOwned
  have initial : property (prepared.state,#[],.Completed) := ⟨rfl,preparedOwned⟩
  have final := DuplicatePrefix.GeneralBorrowLoop.list_invariant _ scan property step
    (prepared.state,#[],.Completed) initial
  exact final.2

end DuplicatePrefix.S02DisjointReadFrame

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02DisjointReadFrame.concrete) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
