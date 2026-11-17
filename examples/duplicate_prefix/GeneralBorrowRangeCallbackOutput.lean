import duplicate_prefix.GeneralBorrowLoopMarked
import duplicate_prefix.GeneralBorrowRange
import duplicate_prefix.GeneralRangeMapCoverage

namespace DuplicatePrefix.GeneralBorrowRangeCallbackOutput
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Exact write-back composition: properties established by EVERY real selected
source callback hold on the FINAL stored requested range. Callback equations
are intermediate certificates, discharged by the caller's initial-data proof;
this helper is not itself a safety theorem with assumed successful calls. -/
theorem outputs (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor : UniIndex)
    (offset len : Size) (kind : AccessKind) (mode : ChildrenVisitMode) (predicate : LocationTree → Prop)
    (present : tree.indexOfTag tag = some anchor) (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (callbacks : ∀ cursor (valid : cursor < (tree.locations.iterMut offset len).segments.size),
      let segment := (tree.locations.iterMut offset len).segments[cursor]
      source_access_status (source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range) = none ∧
        predicate (source_access_location (source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range))) :
    GeneralRangeMapOrigins.OwnedOn predicate offset.bytes (offset.bytes+len.bytes)
      (tree.performBorrowAccessRange (.concrete tag) offset len kind protections mode).tree.locations := by
  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut (fun _ : LocationTree => True) tree.locations offset len well (fun _ _ => True.intro) bounds
  let positionAt := fun (cursor : Nat) => (prepared.positions[cursor]?).getD 0
  let outputAt := fun (cursor : Nat) => ((prepared.segments[cursor]?).map fun segment =>
    source_access_location (source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range)).getD {perms := {},exposedCache := {}}
  unfold BorrowTree.performBorrowAccessRange
  simp only [present,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let good := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size ∧
      state.1.entries.map (·.range) = prepared.state.entries.map (·.range)
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state, good state →
      ∃ (valid : positionAt cursor < state.1.entries.size), ∃ visited,
        scan cursor state = .yield (replaced state.1 (positionAt cursor) valid (outputAt cursor),visited,.Completed) ∧
        good (replaced state.1 (positionAt cursor) valid (outputAt cursor),visited,.Completed) ∧ predicate (outputAt cursor) := by
    intro cursor member state stateGood
    rcases state with ⟨current,visited,status⟩
    rcases stateGood with ⟨statusEq,sizeEq,ranges⟩
    dsimp only at statusEq sizeEq ranges
    subst status
    have cursorBound : cursor < prepared.positions.size := by have := (List.mem_range'_1.mp member).2;omega
    have segmentBound : cursor < prepared.segments.size := by rw [←preparedGood.lengths];exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    have positionEq : positionAt cursor = position := by simp only [positionAt,Array.getElem?_eq_getElem cursorBound,Option.getD_some,position]
    have outputEq : outputAt cursor = source_access_location (source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range) := by
      simp only [outputAt,Array.getElem?_eq_getElem segmentBound,Option.map_some,Option.getD_some,segment]
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have currentBound : positionAt cursor < current.entries.size := by rw [positionEq,sizeEq];exact positionBound
    have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
    have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
    have localGood : source_access_status (source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range) = none ∧
        predicate (source_access_location (source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range)) := callbacks cursor segmentBound
    refine ⟨currentBound,visited.push ⟨segment.range,source_access_normal (source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range)⟩,?_,?_,?_⟩
    · simp only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,setAtPos_success current position (by rw [sizeEq];exact positionBound),localGood.1]
      rw [setAtPos_exact current position (by rw [sizeEq];exact positionBound)]
      simp only [positionEq,outputEq]
    · exact ⟨rfl,(replaced_length current _ currentBound _).trans sizeEq,(replaced_ranges current _ currentBound _).trans ranges⟩
    · rw [outputEq]
      exact localGood.2
  have initial : good (prepared.state,#[],.Completed) := ⟨rfl,rfl,rfl⟩
  have finalGood := GeneralBorrowLoop.list_invariant _ scan good (by
    intro cursor member state stateGood
    obtain ⟨valid,visited,actual,nextGood,_⟩ := step cursor member state stateGood
    simpa only [actual,ForInStep.value] using nextGood) _ initial
  intro query finalValid positive start stop
  have oldValid : query < prepared.state.entries.size := by rw [←finalGood.2.1];exact finalValid
  have localFinalValid : query < (forIn (List.range' 0 prepared.positions.size) (prepared.state,#[],BorrowTree.BorrowTreeAccessStatus.Completed) scan).1.entries.size := finalValid
  have rangeEq : ((forIn (List.range' 0 prepared.positions.size) (prepared.state,#[],BorrowTree.BorrowTreeAccessStatus.Completed) scan).1.entries[query]'finalValid).range =
      (prepared.state.entries[query]'oldValid).range := by
    have selected := congrArg (fun rows => rows[query]?) finalGood.2.2
    simpa only [Array.getElem?_map,Array.getElem?_eq_getElem localFinalValid,Array.getElem?_eq_getElem oldValid,Option.map_some,Option.some.injEq] using selected
  rw [rangeEq] at start stop
  obtain ⟨target,targetBound,targetEq⟩ := GeneralRangeMapCoverage.overlap_selected tree.locations offset len well bounds positive query oldValid start stop
  have targetBoundLocal : target < prepared.positions.size := targetBound
  have targetPosition : positionAt target = query := by
    have selected : prepared.positions[target]? = some query := by
      rw [Array.getElem?_eq_getElem targetBoundLocal]
      exact congrArg some targetEq
    simp only [positionAt,selected,Option.getD_some]
  let has := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    ∃ segment, state.1.entries[query]? = some segment ∧ predicate segment.data
  have sets : ∀ cursor ∈ List.range' 0 prepared.positions.size, cursor = target → ∀ state, good state → has (scan cursor state).value := by
    intro cursor member same state stateGood
    subst cursor
    obtain ⟨valid,visited,actual,nextGood,outGood⟩ := step target member state stateGood
    rw [actual]
    refine ⟨{state.1.entries[positionAt target] with data := outputAt target},?_,outGood⟩
    rw [←targetPosition]
    simp only [ForInStep.value,replaced,Array.getElem?_set_self valid]
  have preserves : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state, good state → has state → has (scan cursor state).value := by
    intro cursor member state stateGood stateHas
    by_cases same : positionAt cursor = query
    · obtain ⟨valid,visited,actual,nextGood,outGood⟩ := step cursor member state stateGood
      rw [actual]
      refine ⟨{state.1.entries[positionAt cursor] with data := outputAt cursor},?_,outGood⟩
      rw [←same]
      simp only [ForInStep.value,replaced,Array.getElem?_set_self valid]
    · obtain ⟨valid,visited,actual,nextGood,outGood⟩ := step cursor member state stateGood
      obtain ⟨segment,found,owned⟩ := stateHas
      rw [actual]
      refine ⟨segment,?_,owned⟩
      simpa only [ForInStep.value,replaced,Array.getElem?_set_ne valid same] using found
  have finished := GeneralBorrowLoopMarked.eventual (List.range' 0 prepared.positions.size) scan good has (fun cursor => cursor = target)
    (by intro cursor member state stateGood;obtain ⟨valid,visited,actual,nextGood,_⟩ := step cursor member state stateGood;exact ⟨_,actual,nextGood⟩)
    sets preserves ⟨target,List.mem_range'.mpr ⟨by omega,by simpa using targetBoundLocal⟩,rfl⟩ _ initial
  obtain ⟨segment,found,owned⟩ := finished.2
  have same : ((forIn (List.range' 0 prepared.positions.size) (prepared.state,#[],BorrowTree.BorrowTreeAccessStatus.Completed) scan).1.entries[query]'finalValid) = segment :=
    Option.some.inj ((Array.getElem?_eq_getElem finalValid).symm.trans found)
  rw [same]
  exact owned

end DuplicatePrefix.GeneralBorrowRangeCallbackOutput
