import duplicate_prefix.GeneralBorrowWildcardSubtreeModeIterator
import duplicate_prefix.GeneralBorrowForestAccessData
import duplicate_prefix.GeneralBorrowRange

namespace DuplicatePrefix.GeneralBorrowForestModeAccess
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState
open GeneralBorrowWildcardSubtreeRegion
open GeneralBorrowForestAccessData (Context)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Per-location initial permissions/cache/finite-forest data. Event exclusion
is a property of the raw topology's traversal schedule, not an access-success
premise. The region may contain arbitrary child-closed extra subtrees. -/
structure LocationData (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode) where
  forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology
  owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind
  rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = primary.toNat
  region : Region tree location kind protections
  supported : ∀ root ∈ extras, region.support root
  outside : ∀ query, region.support query →
    ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse anchor.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2, event.node ≠ query.toNat

/-- The actual per-location source operation completes from the graph and
permission/cache records above. All exposed-node flags are static tree data. -/
theorem local_access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange)
    (context : Context tree anchor primary extras)
    (data : LocationData tree location protections anchor primary extras kind mode) :
    source_access_status (source_tree_access_at tree location (some anchor) kind protections mode range) = none := by
  obtain ⟨after,actual,status,preserved,cache,frame⟩ := GeneralBorrowWildcardSubtreeModeIterator.access tree location protections
    anchor primary context.anchorNode context.primaryNode extras kind mode range data.forest data.owned context.depth context.children
    context.anchorPresent context.primaryPresent context.roots context.different data.rootPath data.region data.supported data.outside
    context.unexposed
  exact status


/-- Real concrete ranged access with arbitrary extra unexposed foreign-owned
subtrees. Interval preparation preserves the initial location-data records;
each actual source call derives its completion from those records. -/
theorem ranged_access (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (anchor primary : UniIndex) (extras : List UniIndex) (offset len : Size) (kind : AccessKind) (mode : ChildrenVisitMode)
    (context : Context tree anchor primary extras)
    (tagPresent : tree.indexOfTag tag = some anchor) (well : tree.locations.WellFormed)
    (all : Every (fun location => Nonempty (LocationData tree location protections anchor primary extras kind mode)) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    let result := tree.performBorrowAccessRange (.concrete tag) offset len kind protections mode
    result.status = .Completed ∧ result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  dsimp only
  let predicate := fun location => Nonempty (LocationData tree location protections anchor primary extras kind mode)
  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut predicate tree.locations offset len well all bounds
  unfold BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size ∧
      state.1.WellFormed ∧ state.1.size = tree.locations.size
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state good
    rcases state with ⟨current,visited,status⟩
    rcases good with ⟨statusEq,sizeEq,wellFormed,capacity⟩
    dsimp only at statusEq sizeEq
    subst status
    have cursorBound : cursor < prepared.positions.size := by
      have bounded := List.mem_range'_1.mp member
      simpa using bounded.2
    have segmentBound : cursor < prepared.segments.size := by rw [←preparedGood.lengths];exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have localData : Nonempty (LocationData tree segment.data protections anchor primary extras kind mode) := by
      rw [show segment = prepared.state.entries[position]'positionBound from selected]
      exact preparedGood.every position positionBound
    obtain ⟨data⟩ := localData
    have accessGood := local_access tree segment.data protections anchor primary extras kind mode segment.range context data
    let accessed := source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range
    let mutation := current.setAtPos position (source_access_location accessed)
    have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
    have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
    have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
    have actual : scan cursor (current,visited,.Completed) =
        .yield (mutation.state,visited.push ⟨segment.range,source_access_normal accessed⟩,.Completed) := by
      simp only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
        setAtPos_success current position currentBound,accessGood]
      rfl
    rw [actual]
    refine ⟨rfl,(setAtPos_length current position currentBound _).trans sizeEq,?_,?_⟩
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_wellFormed current position currentBound _ wellFormed
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact (replaced_size current position currentBound _).trans capacity
  have start : property (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity⟩
  have final := GeneralBorrowLoop.list_invariant _ scan property step _ start
  exact ⟨final.1,final.2.2.1,final.2.2.2⟩

end DuplicatePrefix.GeneralBorrowForestModeAccess
