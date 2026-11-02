import duplicate_prefix.GeneralBorrowProtectedReadExposureCache
import duplicate_prefix.GeneralBorrowProtectedSiblingRootRead
import duplicate_prefix.GeneralBorrowConstructorPriorPermission
import duplicate_prefix.GeneralBorrowProtectedReadSingleRoot
import duplicate_prefix.GeneralBorrowProtectedReadRelease
import duplicate_prefix.GeneralBorrowRangePreserves
import duplicate_prefix.GeneralRangeMapOriginPrepare
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingPartialRangeInvariant
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowExposureCardinality DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Source ranged Read lifts any preserved per-location predicate to every actual output partition. -/
theorem ranged (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (anchor root : UniIndex)
    (offset len : Size) (mode : ChildrenVisitMode)
    (depth : ParentDepth tree.nodes) (children : GeneralBorrowGraph.ChildNodes tree)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode)
    (roots : tree.roots = #[root]) (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (well : tree.locations.WellFormed)
    (predicate : LocationTree → Prop) (all : Every predicate tree.locations)
    (callback : ∀ location,GeneralBorrowProtectedReadRelease.Profile tree protections location → predicate location →
      predicate (tree.performNormalAccessAt location anchor .Read protections mode).location)
    (sliceStart sliceStop : UInt64)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (GeneralBorrowProtectedReadRelease.Profile tree protections) sliceStart sliceStop tree.locations)
    (requestLower : sliceStart.toNat ≤ offset.bytes.toNat)
    (requestUpper : (offset.bytes+len.bytes).toNat ≤ sliceStop.toNat)
    (bounds : offset.bytes.toNat + len.bytes.toNat ≤ tree.locations.size.bytes.toNat) :
    let result := tree.performNormalAccessRange tag offset len .Read protections mode
    result.status = .Completed ∧
      Every predicate result.tree.locations ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size ∧
      result.tree.nodes = tree.nodes ∧ result.tree.roots = tree.roots ∧ result.tree.tagMapping = tree.tagMapping := by
  dsimp only
  let prepared := tree.locations.iterMut offset len
  have preparedGood := GeneralRangeMapSafety.iter_mut predicate tree.locations offset len well all bounds
  have preparedOwners := GeneralRangeMapOriginPrepare.selected_owned_on tree.locations offset len well bounds
    (GeneralBorrowProtectedReadRelease.Profile tree protections) sliceStart sliceStop owned requestLower requestUpper
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
    have ownedHere : GeneralBorrowProtectedReadRelease.Profile tree protections segment.data :=
      preparedOwners.2.2 cursor segmentBound
    obtain ⟨⟨forest⟩,data⟩ := ownedHere
    have valid := GeneralBorrowProtectedReadPermissionMetadata.valid_anchor tree segment.data protections anchor anchorNode anchorPresent
    have compatible := GeneralBorrowProtectedReadPermissionMetadata.compatible_initial tree segment.data protections anchor data
    have updatedCache : predicate
        (source_access_location (source_tree_access_at tree segment.data (some anchor) .Read protections mode segment.range)) := by
      rw [GeneralBorrowProtectedReadSingleRoot.single_root_location tree segment.data protections anchor root mode segment.range
        forest valid compatible depth children anchorNode anchorPresent roots covered]
      exact callback segment.data ⟨⟨forest⟩,data⟩ cacheHere
    have accessGood := GeneralBorrowProtectedReadSingleRoot.access_at tree segment.data protections anchor root mode segment.range
      forest valid compatible depth children anchorNode anchorPresent roots covered
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
  exact ⟨final.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2,trivial,trivial,trivial⟩
end DuplicatePrefix.GeneralBorrowProtectedSiblingPartialRangeInvariant
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedSiblingPartialRangeInvariant.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected Read ranged cache dependency {dependency}"
