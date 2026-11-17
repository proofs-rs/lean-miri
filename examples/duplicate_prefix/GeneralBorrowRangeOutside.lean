import duplicate_prefix.GeneralBorrowConcreteRangeInvariant
import duplicate_prefix.GeneralBorrowFreshReadFrame
import duplicate_prefix.GeneralRangeMapByteLookup

/-! Physical-byte framing for the actual ranged Tree Borrows operation.
Segment vector positions may change during preparation; the observable here
is the value returned at one physical byte, independent of operation status. -/
namespace DuplicatePrefix.GeneralBorrowRangeOutside
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralRangeMapOrigins GeneralRangeMapGeometry RangeMapNonempty
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

private structure RowFrame (prepared current : DedupRangeMap LocationTree) (point : UInt64) : Prop where
  length : current.entries.size = prepared.entries.size
  well : current.WellFormed
  capacity : current.size = prepared.size
  ranges : ∀ index (valid : index < current.entries.size),
    current.entries[index].range = (prepared.entries[index]'(by rw [←length];exact valid)).range
  data : ∀ index (valid : index < current.entries.size),
    current.entries[index].range.start.toNat ≤ point.toNat →
    point.toNat < current.entries[index].range.stop.toNat →
    current.entries[index].data = (prepared.entries[index]'(by rw [←length];exact valid)).data

private theorem row_refl (map : DedupRangeMap LocationTree) (well : map.WellFormed) (point : UInt64) :
    RowFrame map map point := ⟨rfl,well,rfl,fun _ _ => rfl,fun _ _ _ _ => rfl⟩

private theorem row_replace (prepared current : DedupRangeMap LocationTree) (point : UInt64)
    (frame : RowFrame prepared current point) (position : Nat) (valid : position < current.entries.size)
    (data : LocationTree) (excluded : ¬ Contains prepared point position) :
    RowFrame prepared (replaced current position valid data) point := by
  refine ⟨(replaced_length current position valid data).trans frame.length,
    replaced_wellFormed current position valid data frame.well,
    (replaced_size current position valid data).trans frame.capacity,?_,?_⟩
  · intro index bounded
    have oldBound : index < current.entries.size := by simpa only [replaced_length] using bounded
    exact (replaced_range current position valid data index oldBound).trans (frame.ranges index oldBound)
  · intro index bounded start stop
    have oldBound : index < current.entries.size := by simpa only [replaced_length] using bounded
    rw [replaced_range current position valid data index oldBound] at start stop
    by_cases same : position = index
    · subst index
      apply False.elim
      apply excluded
      refine ⟨by rw [←frame.length];exact valid,?_,?_⟩
      · rw [←frame.ranges position valid];exact start
      · rw [←frame.ranges position valid];exact stop
    · simpa only [replaced,Array.getElem_set_ne _ oldBound same] using frame.data index oldBound start stop

private theorem row_value (prepared current : DedupRangeMap LocationTree) (point : UInt64)
    (frame : RowFrame prepared current point) (value : LocationTree)
    (observed : ValueAt current point value) : ValueAt prepared point value := by
  obtain ⟨index,valid,start,stop,data⟩ := observed
  refine ⟨index,by rw [←frame.length];exact valid,?_,?_,?_⟩
  · rw [←frame.ranges index valid];exact start
  · rw [←frame.ranges index valid];exact stop
  · exact (frame.data index valid start stop).symm.trans data

private abbrev AccessState := DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus

/-- The actual range-loop body, factored locally for its data-frame proof.
The public theorem below unfolds the production operation and checks this
body definitionally; every status/error branch is retained. -/
private def accessScan (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (source : Option UniIndex) (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (cursor : Nat) (state : AccessState) : Id (ForInStep AccessState) := Id.run do
  let mut current := state.1
  let mut visited := state.2.1
  let mut status := state.2.2
  if status == .Completed then
    match prepared.positions[cursor]?, prepared.segments[cursor]? with
    | some position, some segment =>
        let access := source_tree_access_at tree segment.data source kind protections mode segment.range
        let mutation := current.setAtPos position (source_access_location access)
        current := mutation.state
        visited := visited.push ⟨segment.range,source_access_normal access⟩
        match mutation.outcome with
        | .error error => status := .LocationMapFailure segment.range error
        | .ok () =>
            match source_access_status access with
            | some failure => status := failure
            | none => pure ()
    | _, _ => status := .RangeMapFailure (.indexOutOfBounds cursor prepared.positions.size)
  return .yield (current,visited,status)

private theorem scan_frame (tree : BorrowTree) (prepared : IterMutResult LocationTree)
    (good : GeneralRangeMapPrepared.Good (fun _ : LocationTree => True) tree.locations.size.bytes prepared)
    (lower upper point : UInt64) (within : GeneralRangeMapOriginPrepare.Within prepared lower upper)
    (outside : point.toNat < lower.toNat ∨ upper.toNat ≤ point.toNat)
    (source : Option UniIndex) (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode) :
    RowFrame prepared.state
      (forIn (List.range' 0 prepared.positions.size) (prepared.state,#[],.Completed)
        (accessScan tree prepared source kind protections mode)).1 point := by
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state : AccessState,
      RowFrame prepared.state state.1 point →
      RowFrame prepared.state (accessScan tree prepared source kind protections mode cursor state).value.1 point := by
    intro cursor member state frame
    rcases state with ⟨current,visited,status⟩
    by_cases active : status = .Completed
    · subst status
      have cursorBound : cursor < prepared.positions.size := by
        have bounded := List.mem_range'_1.mp member
        simpa using bounded.2
      have segmentBound : cursor < prepared.segments.size := by rw [←good.lengths];exact cursorBound
      let position := prepared.positions[cursor]'cursorBound
      let segment := prepared.segments[cursor]'segmentBound
      obtain ⟨positionBound,selection⟩ := good.selected cursor cursorBound
      have currentBound : position < current.entries.size := by rw [frame.length];exact positionBound
      have excluded : ¬ Contains prepared.state point position := by
        intro present
        obtain ⟨_,start,stop⟩ := present
        have geometry : lower.toNat ≤ segment.range.start.toNat ∧ segment.range.stop.toNat ≤ upper.toNat :=
          within cursor segmentBound
        have same : segment = prepared.state.entries[position]'positionBound := selection
        rw [←same] at start stop
        rcases outside with before | after <;> omega
      have preserved (data : LocationTree) : RowFrame prepared.state (replaced current position currentBound data) point :=
        row_replace prepared.state current point frame position currentBound data excluded
      have positionLookup : prepared.positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
      have segmentLookup : prepared.segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
      simp only [accessScan,Id.run,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
        setAtPos_exact current position currentBound,pure]
      split <;> exact preserved _
    · have stopped : (status == .Completed) = false := by cases status <;> simp_all
      simpa only [accessScan,Id.run,stopped,Bool.false_eq_true,↓reduceIte,pure,ForInStep.value] using frame
  exact GeneralBorrowLoop.list_invariant _ (accessScan tree prepared source kind protections mode)
    (fun state : AccessState => RowFrame prepared.state state.1 point) step _
    (row_refl prepared.state good.wellFormed point)

/-- The production ranged operation preserves well-formedness, size and the
raw value at every physical byte outside its requested half-open interval.
Access completion is deliberately not a premise or conclusion. -/
theorem outside_frame (tree : BorrowTree) (provenance : ProvenanceExtra) (offset len : Size)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (point : UInt64)
    (outside : point.toNat < offset.bytes.toNat ∨ (offset.bytes+len.bytes).toNat ≤ point.toNat) :
    let result := tree.performBorrowAccessRange provenance offset len kind protections mode
    result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size ∧
      ∀ value, ValueAt result.tree.locations point value → ValueAt tree.locations point value := by
  let prepared := tree.locations.iterMut offset len
  have preparation := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have good := preparation.1
  have finish (source : Option UniIndex) :
      let result := forIn (List.range' 0 prepared.positions.size) (prepared.state,#[],.Completed)
        (accessScan tree prepared source kind protections mode)
      result.1.WellFormed ∧ result.1.size = tree.locations.size ∧
        ∀ value, ValueAt result.1 point value → ValueAt tree.locations point value := by
    have frame := scan_frame tree prepared good offset.bytes (offset.bytes+len.bytes) point preparation.2.2 outside source kind protections mode
    refine ⟨frame.well,frame.capacity.trans (congrArg Size.ofBytes good.capacity),?_⟩
    intro value observed
    exact preparation.2.1 point value (row_value prepared.state _ point frame value observed)
  cases provenance with
  | concrete tag =>
    cases found : tree.indexOfTag tag with
    | none =>
      simpa only [BorrowTree.performBorrowAccessRange,found,Option.isNone_none,↓reduceIte,Id.run,pure]
        using (show tree.locations.WellFormed ∧ tree.locations.size = tree.locations.size ∧
          ∀ value, ValueAt tree.locations point value → ValueAt tree.locations point value from ⟨well,rfl,fun _ value => value⟩)
    | some source =>
      simp only [BorrowTree.performBorrowAccessRange,found,Option.isNone_some,Bool.false_eq_true,↓reduceIte,
        Id.run,bind,pure,good.outcome,Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
        Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
      name_borrow_range_scan
      have sourceScan : scan = accessScan tree prepared (some source) kind protections mode := by
        funext cursor state
        rfl
      rw [sourceScan]
      exact finish (some source)
  | wildcard =>
      simp only [BorrowTree.performBorrowAccessRange,Id.run,bind,pure,good.outcome,
        Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
        Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
      name_borrow_range_scan
      have sourceScan : scan = accessScan tree prepared none kind protections mode := by
        funext cursor state
        rfl
      rw [sourceScan]
      exact finish none

/-- Observable lookup equality at an in-allocation byte, independent of the
operation's success or failure and of preparation's split/merge indexing. -/
theorem lookup_outside (tree : BorrowTree) (provenance : ProvenanceExtra) (offset len : Size)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (well : tree.locations.WellFormed)
    (bounds : offset.bytes.toNat+len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (point : UInt64) (inside : point.toNat < tree.locations.size.bytes.toNat)
    (outside : point.toNat < offset.bytes.toNat ∨ (offset.bytes+len.bytes).toNat ≤ point.toNat) :
    GeneralRangeMapByteLookup.lookup (tree.performBorrowAccessRange provenance offset len kind protections mode).tree.locations point =
      GeneralRangeMapByteLookup.lookup tree.locations point := by
  have frame := outside_frame tree provenance offset len kind protections mode well bounds point outside
  exact GeneralRangeMapByteLookup.equal_of_refines _ _ well frame.1 frame.2.1 point frame.2.2 inside

end DuplicatePrefix.GeneralBorrowRangeOutside
