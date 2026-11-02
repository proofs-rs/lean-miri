import duplicate_prefix.GeneralBorrowObserverDirectReadNormal
import duplicate_prefix.GeneralBorrowObserverReadRow
namespace DuplicatePrefix.GeneralBorrowObserverDirectReadRow
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess
open GeneralBorrowReadRowNormal (ReadRow)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Actual direct shared-parent Read including every other-root callback retains
its mutable observer under the current real Strong registration table. -/
theorem access (tree : BorrowTree) (location : LocationTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (observer : UniIndex) (observerNode : TreeNode)
    (edge : anchorNode.parent = some observer) (observerPresent : tree.nodeAt observer = some observerNode)
    (hidden : anchorNode.isExposed = false) (unprotected : global.protectedTags.contains anchorNode.tag = false)
    (observerBoth : DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags observer)
    (observerPath : ((source_normal_projection tree location global.protectedTags).topology.ancestorPath observer.toNat).getLast? = some selected.toNat)
    (maximum : Option BorTag)
    (row : ReadRow tree location global.protectedTags (some anchor) (some selected) maximum)
    (distinct : tree.roots.toList.Nodup)
    (order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] →
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location global.protectedTags)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location global.protectedTags)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location (some anchor) .Read global.protectedTags mode range
    source_access_status result = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) global.protectedTags ∧
    GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) global.protectedTags ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
    Nonempty (ReadRow tree (source_access_location result) global.protectedTags (some anchor) (some selected) maximum) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree (source_access_location result)
      global.protectedTags observer) := by
  obtain ⟨done,outcome,cache,sifa,gp,afterRow⟩ := GeneralBorrowReadRowNormal.access tree location global.protectedTags runtime.formed.toGraphState anchor selected anchorNode present maximum row coherent profile possible short mode
  obtain ⟨sourceNormal⟩ := row.normal anchor rfl
  obtain ⟨_,_,⟨observerAfter⟩⟩ := GeneralBorrowObserverDirectReadNormal.access tree location global runtime
    anchor observer anchorNode present edge hidden unprotected sourceNormal observerBoth mode
  have path : ((source_normal_projection tree location global.protectedTags).topology.ancestorPath anchor.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD, row.rootPath anchor rfl]
    rfl
  have rootEq : (tree.performNormalAccessAt location anchor .Read global.protectedTags mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ .Read (source_normal_projection tree location global.protectedTags)).trans path
  obtain ⟨selectedNode,selectedPresent⟩ := row.rootPresent selected rfl
  have selectedLookup : tree.nodes.get selected = some selectedNode := selectedPresent
  have cutoff : maximum = some selectedNode.tag := by simpa [selectedPresent] using row.cutoff
  let property := fun current =>
    GeneralBorrowExposureCardinality.LocationCoherent tree current global.protectedTags ∧
    GeneralBorrowLocationSifaConsistency.Profile tree current global.protectedTags ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current ∧
    Nonempty (ReadRow tree current global.protectedTags (some anchor) (some selected) maximum) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree current global.protectedTags observer)
  have steps : ∀ position (valid : position < tree.roots.size), selected ≠ tree.roots[position] →
      ∀ current, property current →
      let result := tree.performWildcardAccessAt current tree.roots[position] maximum .Read global.protectedTags (position != 0)
      result.status = .Completed ∧ property result.location := by
    intro position valid different current good
    obtain ⟨cache,sifa,gp,⟨currentRow⟩,⟨currentObserver⟩⟩ := good
    apply GeneralBorrowObserverReadRow.callback tree current global.protectedTags global.protectedTags
      runtime.formed.toGraphState anchor observer selected anchorNode observerNode present observerPresent maximum currentRow
      currentObserver observerPath distinct position valid different _ cache sifa gp short
    intro primary
    subst position
    exact order valid different
  have final := GeneralBorrowConcreteRootInvariant.roots tree global.protectedTags selected maximum
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree anchor else none) .Read mode range property steps
    ((tree.performNormalAccessAt location anchor .Read global.protectedTags mode).location,none,false)
    ⟨rfl,cache,sifa,gp,afterRow,⟨observerAfter⟩⟩
  dsimp only
  simp_tree_helpers
  simp only [done,outcome,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedLookup,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  dsimp only [property] at final
  rw [cutoff] at final ⊢
  let after : Id GeneralBorrowConcreteRowAccess.State := forIn (List.range' 0 tree.roots.size)
    ((tree.performNormalAccessAt location anchor .Read global.protectedTags mode).location,none,false)
    (GeneralBorrowConcreteRowAccess.scan tree selected (some selectedNode.tag)
      (if mode == .SkipChildrenOfAccessed then source_min_exposed tree anchor else none) .Read global.protectedTags mode range)
  change after.2.1 = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree after.1 global.protectedTags ∧
    GeneralBorrowLocationSifaConsistency.Profile tree after.1 global.protectedTags ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree after.1 ∧
    Nonempty (ReadRow tree after.1 global.protectedTags (some anchor) (some selected) (some selectedNode.tag)) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree after.1 global.protectedTags observer)
  exact final
end DuplicatePrefix.GeneralBorrowObserverDirectReadRow
