import duplicate_prefix.GeneralBorrowRootAuthorityReadLocation
import duplicate_prefix.GeneralBorrowStructuralHistoryRootAuthorityState
import duplicate_prefix.GeneralBorrowFreshReadFrame
import duplicate_prefix.GeneralBorrowPhysicalReadableLocation
import duplicate_prefix.GeneralBorrowPhysicalReadableProtections
import duplicate_prefix.GeneralBorrowProtectedReadSingleRoot
import duplicate_prefix.GeneralBorrowProtectedReadRelease
import duplicate_prefix.GeneralBorrowRangePreserves
import duplicate_prefix.GeneralRangeMapOriginPrepare
namespace DuplicatePrefix.GeneralBorrowRootAuthorityReadRange
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual bounded concrete parent Read preserves full physical readability and graph metadata. -/
theorem ranged (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor root : UniIndex)
    (offset len : Size) (mode : ChildrenVisitMode)
    (fits : tree.nodes.data.size ≤ 4294967296) (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode rootNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (rootPresent : tree.nodeAt root = some rootNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (well : tree.locations.WellFormed)
    (forest : ∀ location, GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (all : Every (fun location => GeneralBorrowPhysicalReadable.Profile tree location protections ∧
      GeneralBorrowStructuralHistoryRootAuthorityAt.At tree location root) tree.locations)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    let result := tree.performNormalAccessRange tag offset len .Read protections mode
    result.status = .Completed ∧
      Every (fun location => GeneralBorrowPhysicalReadable.Profile result.tree location protections ∧
        GeneralBorrowStructuralHistoryRootAuthorityAt.At result.tree location root) result.tree.locations ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size ∧
      result.tree.nodes = tree.nodes ∧ result.tree.roots = tree.roots ∧ result.tree.tagMapping = tree.tagMapping := by
  dsimp only
  let predicate := fun location => GeneralBorrowPhysicalReadable.Profile tree location protections ∧
    GeneralBorrowStructuralHistoryRootAuthorityAt.At tree location root
  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut predicate tree.locations offset len well all bounds
  unfold BorrowTree.performNormalAccessRange BorrowTree.performBorrowAccessRange
  simp only [tagPresent,Option.isNone_some,Bool.false_eq_true,↓reduceIte]
  simp only [Id.run,bind,pure,preparedGood.outcome]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,
    Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  name_borrow_range_scan
  let property := fun state : DedupRangeMap LocationTree × Array BorrowTree.BorrowTreeLocationResult × BorrowTree.BorrowTreeAccessStatus =>
    state.2.2 = .Completed ∧ state.1.entries.size = prepared.state.entries.size ∧
      Every predicate state.1 ∧ state.1.WellFormed ∧ state.1.size = tree.locations.size
  have step : ∀ cursor ∈ List.range' 0 prepared.positions.size, ∀ state,
      property state → property (scan cursor state).value := by
    intro cursor member state good
    rcases state with ⟨current,visited,status⟩
    rcases good with ⟨statusEq,sizeEq,every,wellFormed,capacity⟩
    dsimp only at statusEq sizeEq
    subst status
    have cursorBound : cursor < prepared.positions.size := by
      have bounded := List.mem_range'_1.mp member
      simpa using bounded.2
    have segmentBound : cursor < prepared.segments.size := by rw [←preparedGood.lengths];exact cursorBound
    let position := prepared.positions[cursor]'cursorBound
    let segment := prepared.segments[cursor]'segmentBound
    obtain ⟨positionBound,selected⟩ := preparedGood.selected cursor cursorBound
    have cacheHere : predicate segment.data := by
      rw [show segment = prepared.state.entries[position]'positionBound from selected]
      exact preparedGood.every position positionBound
    have operation := GeneralBorrowPhysicalReadableLocation.location tree segment.data protections anchor root mode segment.range
      (forest segment.data) fits depth children anchorNode anchorPresent roots covered cacheHere.1
    have authority := GeneralBorrowRootAuthorityReadLocation.single_root tree segment.data protections root anchor rootNode anchorNode
      rootPresent anchorPresent mode segment.range (forest segment.data) fits depth children roots covered cacheHere.1 cacheHere.2
    have updatedCache : predicate
        (source_access_location (source_tree_access_at tree segment.data (some anchor) .Read protections mode segment.range)) := ⟨operation.2,authority.2⟩
    have accessGood := operation.1
    let access := source_tree_access_at tree segment.data (some anchor) .Read protections mode segment.range
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
    refine ⟨rfl,(setAtPos_length current position currentBound _).trans sizeEq,?_,?_,?_⟩
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_every predicate current position currentBound _ every updatedCache
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact replaced_wellFormed current position currentBound _ wellFormed
    · dsimp only [mutation]
      rw [setAtPos_exact current position currentBound]
      exact (replaced_size current position currentBound _).trans capacity
  have initial : property (prepared.state,#[],.Completed) :=
    ⟨rfl,rfl,preparedGood.every,preparedGood.wellFormed,congrArg Size.ofBytes preparedGood.capacity⟩
  have final := GeneralBorrowLoop.list_invariant _ scan property step _ initial
  refine ⟨final.1,?_,final.2.2.2.1,final.2.2.2.2,trivial,trivial,trivial⟩
  intro position valid
  obtain ⟨physical,authority⟩ := final.2.2.1 position valid
  exact ⟨GeneralBorrowPhysicalReadableProtections.nodes tree _ _ protections rfl physical,authority.present,authority.vacant⟩
end DuplicatePrefix.GeneralBorrowRootAuthorityReadRange
