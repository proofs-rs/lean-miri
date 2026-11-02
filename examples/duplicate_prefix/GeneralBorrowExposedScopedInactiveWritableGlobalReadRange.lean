import duplicate_prefix.GeneralBorrowFreshActiveOnClean
import duplicate_prefix.GeneralBorrowRangeLocal
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadClosed
import duplicate_prefix.GeneralBorrowSifaWritableFrame
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableGlobalReadRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowFreshActiveOnClean
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]

/-- Concrete parent Read preserves allocation-wide mixed writable old-leaf profiles and
coherent caches while borrowing only the requested owned window. No ownership
is requested outside that window. -/
theorem ranged (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor selected head : UniIndex)
    (tail : List UniIndex) (offset len : Size)
    (context : GeneralBorrowExposedKnownRootRangeData.Context tree anchor selected head tail)
    (support : Nat → Prop) (writable : Nat → Bool) (fits : tree.nodes.data.size ≤ 4294967296)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (clean : Every (fun location : LocationTree => GeneralBorrowExposureCardinality.LocationCoherent tree location protections ∧
      GeneralBorrowSifaWritableFrame.Profile tree protections area.support location ∧ GeneralBorrowExposedInactiveConstructor.Profile tree location anchor support) tree.locations)
    (well : tree.locations.WellFormed) (sliceStart sliceStop : UInt64)
    (owned : OwnedOn ((fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location protections anchor selected head tail support writable))) sliceStart sliceStop tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes+len.bytes).toNat ≤ sliceStop.toNat) :
    let result := tree.performNormalAccessRange tag offset len .Read protections .VisitChildrenOfAccessed
    result.status = .Completed ∧
      Every (fun location : LocationTree => GeneralBorrowExposureCardinality.LocationCoherent tree location protections ∧ GeneralBorrowSifaWritableFrame.Profile tree protections area.support location ∧ GeneralBorrowExposedInactiveConstructor.Profile tree location anchor support) result.tree.locations := by
  dsimp only
  let predicate := (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data tree location protections anchor selected head tail support writable))
  let prepared := tree.locations.iterMut offset len
  have preparedData := GeneralRangeMapOriginPrepare.iter_mut tree.locations offset len well bounds
  have preparedGood := preparedData.1
  have preparedClean := GeneralRangeMapSafety.iter_mut (fun location : LocationTree => GeneralBorrowExposureCardinality.LocationCoherent tree location protections ∧ GeneralBorrowSifaWritableFrame.Profile tree protections area.support location ∧ GeneralBorrowExposedInactiveConstructor.Profile tree location anchor support)
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
      Every (fun location : LocationTree => GeneralBorrowExposureCardinality.LocationCoherent tree location protections ∧ GeneralBorrowSifaWritableFrame.Profile tree protections area.support location ∧ GeneralBorrowExposedInactiveConstructor.Profile tree location anchor support) state.1
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
    obtain ⟨positionBound,segmentSelected⟩ := preparedGood.selected cursor cursorBound
    have ownedHere : predicate segment.data := preparedOwners.2.2 cursor segmentBound
    obtain ⟨data⟩ := ownedHere
    have accessGood := (GeneralBorrowExposedScopedInactiveWritableReadClosed.access tree segment.data protections anchor selected head tail segment.range context support writable fits data).1
    have accessClean : GeneralBorrowExposureCardinality.LocationCoherent tree
        (source_access_location (source_tree_access_at tree segment.data (some anchor) .Read protections .VisitChildrenOfAccessed segment.range)) protections ∧
        GeneralBorrowSifaWritableFrame.Profile tree protections area.support
          (source_access_location (source_tree_access_at tree segment.data (some anchor) .Read protections .VisitChildrenOfAccessed segment.range)) ∧
        GeneralBorrowExposedInactiveConstructor.Profile tree
          (source_access_location (source_tree_access_at tree segment.data (some anchor) .Read protections .VisitChildrenOfAccessed segment.range)) anchor support := by
      obtain ⟨post⟩ := (GeneralBorrowExposedScopedInactiveWritableReadClosed.access tree segment.data protections anchor selected head tail segment.range context support writable fits data).2
      exact ⟨post.base.base.coherent,post.writableLeaves,(GeneralBorrowExposedScopedInactiveMixedRangeData.initial post.base).2.2.1⟩
    let access := source_tree_access_at tree segment.data (some anchor) .Read protections .VisitChildrenOfAccessed segment.range
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
    exact replaced_every (fun location : LocationTree => GeneralBorrowExposureCardinality.LocationCoherent tree location protections ∧ GeneralBorrowSifaWritableFrame.Profile tree protections area.support location ∧ GeneralBorrowExposedInactiveConstructor.Profile tree location anchor support)
      current position currentBound _ every accessClean
  have initial : property (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedClean.every⟩
  have final := GeneralBorrowLoop.list_invariant _ scan property step _ initial
  exact ⟨final.1,final.2.2⟩
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableGlobalReadRange
