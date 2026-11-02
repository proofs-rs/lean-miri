import duplicate_prefix.GeneralBorrowFreshActiveOnClean
import duplicate_prefix.GeneralBorrowRangeLocal
namespace DuplicatePrefix.GeneralBorrowFreshActiveOnRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshActiveOnClean
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A successful ranged parent access retains permission-slot cleanliness for
an append or vacant reusable node index. Permission ownership is required only
on the borrowed slice, while absence of this fresh slot is allocation-wide.
Access completion follows from those data invariants rather than a premise. -/
theorem ranged (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor root query : UniIndex)
    (offset len : Size) (kind ownerKind : AccessKind) (mode : ChildrenVisitMode)
    (allowed : ownerKind = .Read → kind = .Read)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (vacant : tree.nodes.get query = none)
    (clean : Every (fun location : LocationTree => location.perms.get query = none) tree.locations)
    (well : tree.locations.WellFormed) (sliceStart sliceStop : UInt64)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections anchor ownerKind) sliceStart sliceStop tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes+len.bytes).toNat ≤ sliceStop.toNat) :
    let result := tree.performNormalAccessRange tag offset len kind protections mode
    result.status = .Completed ∧
      Every (fun location : LocationTree => location.perms.get query = none) result.tree.locations := by
  dsimp only
  let predicate := GeneralBorrowRange.LocationOwned tree protections anchor ownerKind
  let prepared := tree.locations.iterMut offset len
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedGood := preparedData.1
  have preparedClean := GeneralRangeMapSafety.iter_mut (fun location : LocationTree => location.perms.get query = none)
    tree.locations offset len well clean bounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    predicate sliceStart sliceStop owned requestLower requestUpper
  unfold BorrowTree.performNormalAccessRange BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size ∧
      Every (fun location : LocationTree => location.perms.get query = none) state.1
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state good
    rcases state with ⟨current,visited,status⟩
    rcases good with ⟨statusEq,sizeEq,every⟩
    dsimp only at statusEq sizeEq
    subst status
    have cursorBound : cursor < prepared.positions.size := by
      have bounded := List.mem_range'_1.mp member
      simpa using bounded.2
    have segmentBound : cursor < prepared.segments.size := by rw [←preparedGood.lengths];exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have ownedHere : predicate segment.data := preparedOwners.2.2 cursor segmentBound
    obtain ⟨⟨forest⟩,owner⟩ := ownedHere
    have accessGood := GeneralBorrowSingleRoot.access_at tree segment.data protections anchor root kind mode segment.range
      forest (GeneralBorrowRangePreserves.owned_for_access _ anchor.toNat kind ownerKind allowed owner)
      depth children anchorNode anchorPresent roots covered
    have accessClean : (source_access_location (source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range)).perms.get query = none := by
      rw [GeneralBorrowRangePreserves.single_root_location tree segment.data protections anchor root kind mode segment.range
        forest (GeneralBorrowRangePreserves.owned_for_access _ anchor.toNat kind ownerKind allowed owner)
        depth children anchorNode anchorPresent roots covered]
      apply normal_vacant tree segment.data protections anchor query kind mode depth children anchorNode anchorPresent vacant
      rw [show segment = prepared.state.entries[position]'positionBound from selected]
      exact preparedClean.every position positionBound
    let access := source_tree_access_at tree segment.data (some anchor) kind protections mode segment.range
    let mutation := current.setAtPos position (source_access_location access)
    have currentBound : position < current.entries.size := by rw [sizeEq];exact positionBound
    have positionLookup : (tree.locations.iterMut offset len).positions[cursor]? = some position := Array.getElem?_eq_getElem cursorBound
    have segmentLookup : (tree.locations.iterMut offset len).segments[cursor]? = some segment := Array.getElem?_eq_getElem segmentBound
    have actual : scan cursor (current,visited,.Completed) =
        .yield (mutation.state,visited.push ⟨segment.range,source_access_normal access⟩,.Completed) := by
      simp only [scan,beq_self_eq_true,↓reduceIte,positionLookup,segmentLookup,
        setAtPos_success current position currentBound,accessGood]
      rfl
    rw [actual]
    refine ⟨rfl,(setAtPos_length current position currentBound _).trans sizeEq,?_⟩
    dsimp only [mutation]
    rw [setAtPos_exact current position currentBound]
    exact replaced_every (fun location : LocationTree => location.perms.get query = none)
      current position currentBound _ every accessClean
  have initial : property (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedClean.every⟩
  have final := GeneralBorrowLoop.list_invariant _ scan property step _ initial
  exact ⟨final.1,final.2.2⟩
end DuplicatePrefix.GeneralBorrowFreshActiveOnRange
