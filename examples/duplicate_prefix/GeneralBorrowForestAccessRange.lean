import duplicate_prefix.GeneralBorrowForestAccessData
import duplicate_prefix.GeneralBorrowRange

namespace DuplicatePrefix.GeneralBorrowForestAccessRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralRangeMapState
open GeneralBorrowForestAccessData
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Real concrete ranged access with arbitrary extra unexposed foreign-owned
subtrees. Interval preparation preserves the initial location-data records;
each actual source call derives its completion from those records. -/
theorem access (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag)
    (anchor primary : UniIndex) (extras : List UniIndex) (offset len : Size) (kind : AccessKind)
    (context : Context tree anchor primary extras)
    (tagPresent : tree.indexOfTag tag = some anchor) (well : tree.locations.WellFormed)
    (all : Every (fun location => Nonempty (LocationData tree location protections anchor primary extras kind)) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    let result := tree.performBorrowAccessRange (.concrete tag) offset len kind protections .VisitChildrenOfAccessed
    result.status = .Completed ∧ result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  dsimp only
  let predicate := fun location => Nonempty (LocationData tree location protections anchor primary extras kind)
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
    have localData : Nonempty (LocationData tree segment.data protections anchor primary extras kind) := by
      rw [show segment = prepared.state.entries[position]'positionBound from selected]
      exact preparedGood.every position positionBound
    obtain ⟨data⟩ := localData
    have accessGood := local_access tree segment.data protections anchor primary extras kind segment.range context data
    let accessed := source_tree_access_at tree segment.data (some anchor) kind protections .VisitChildrenOfAccessed segment.range
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

end DuplicatePrefix.GeneralBorrowForestAccessRange
