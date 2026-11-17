import duplicate_prefix.GeneralBorrowFreshRootScopedNormal
import duplicate_prefix.GeneralBorrowFreshRootScopedPrimary
import duplicate_prefix.GeneralBorrowFreshRootScopedVirtual
import duplicate_prefix.GeneralBorrowConcreteRootInvariant
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedAccess
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Literal concrete Read/Write uses the existing general root iterator with
scoped current-row invariants. Global parent tag order is unnecessary. -/
theorem access_when_primary (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (maximum : BorTag) (kind : AccessKind)
    (row : GeneralBorrowFreshRootScopedRow.Row tree location protections anchor selected maximum)
    (distinct : tree.roots.toList.Nodup)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location protections)
    (profile : GeneralBorrowLocationSifaConsistency.Profile tree location protections)
    (possible : GeneralBorrowSnapshotReadRuntime.GlobalPossible tree location)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let result := source_tree_access_at tree location (some anchor) kind protections mode range
    source_access_status result = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree (source_access_location result) protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree (source_access_location result) protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree (source_access_location result) ∧
    Nonempty (GeneralBorrowFreshRootScopedRow.Row tree (source_access_location result) protections anchor selected maximum) := by
  obtain ⟨done,outcome,cache,sifa,gp,afterRow⟩ := GeneralBorrowFreshRootScopedNormal.access tree location protections formed
    anchor selected anchorNode present maximum row kind mode coherent profile possible short
  have path : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = selected.toNat := by
    rw [List.getLast!_eq_getLast?_getD,row.base.rootPath anchor rfl]
    rfl
  have rootEq : (tree.performNormalAccessAt location anchor kind protections mode).access.root = selected.toNat :=
    (GeneralBorrowStorage.events_root _ _ kind (source_normal_projection tree location protections)).trans path
  obtain ⟨selectedNode,selectedPresent⟩ := row.base.rootPresent selected rfl
  have selectedLookup : tree.nodes.get selected = some selectedNode := selectedPresent
  have cutoff : maximum = selectedNode.tag := by
    have known : some maximum = some selectedNode.tag := by simpa [selectedPresent] using row.base.cutoff
    exact Option.some.inj known
  let property := fun current =>
    GeneralBorrowExposureCardinality.LocationCoherent tree current protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree current protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree current ∧
    Nonempty (GeneralBorrowFreshRootScopedRow.Row tree current protections anchor selected maximum)
  have steps : ∀ position,(valid : position < tree.roots.size) → selected ≠ tree.roots[position] →
      ∀ current,property current →
      let result := tree.performWildcardAccessAt current tree.roots[position] (some maximum) kind protections (position != 0)
      result.status = .Completed ∧ property result.location := by
    intro position valid different current good
    obtain ⟨currentCache,currentSifa,currentPossible,⟨currentRow⟩⟩ := good
    by_cases primary : position = 0
    · subst position
      obtain ⟨a,b,c,d,_,e⟩ := GeneralBorrowFreshRootScopedPrimary.access tree current protections formed anchor selected anchorNode present maximum
        currentRow distinct valid different kind currentCache currentSifa currentPossible short
      exact ⟨a,b,c,d,e⟩
    · obtain ⟨a,b,c,d,_,e⟩ := GeneralBorrowFreshRootScopedVirtual.access tree current protections formed anchor selected anchorNode present maximum
        currentRow distinct position valid primary different kind currentCache currentSifa currentPossible short
      have virtual : (position != 0) = true := by simp [primary]
      simp only [virtual]
      exact ⟨a,b,c,d,e⟩
  have final := GeneralBorrowConcreteRootInvariant.roots tree protections selected (some maximum)
    (if mode == .SkipChildrenOfAccessed then source_min_exposed tree anchor else none) kind mode range property steps
    ((tree.performNormalAccessAt location anchor kind protections mode).location,none,false) ⟨rfl,cache,sifa,gp,afterRow⟩
  dsimp only
  simp_tree_helpers
  simp only [done,outcome,rootEq,GeneralBorrowProjection.index_self,Option.bind_some,selectedLookup,Option.map_some]
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',Std.Legacy.Range.size,Nat.sub_zero,Nat.add_sub_cancel,Nat.div_one]
  dsimp only [property] at final
  rw [cutoff] at final ⊢
  let after : Id GeneralBorrowConcreteRowAccess.State := forIn (List.range' 0 tree.roots.size)
    ((tree.performNormalAccessAt location anchor kind protections mode).location,none,false)
    (GeneralBorrowConcreteRowAccess.scan tree selected (some selectedNode.tag)
      (if mode == .SkipChildrenOfAccessed then source_min_exposed tree anchor else none) kind protections mode range)
  change after.2.1 = none ∧
    GeneralBorrowExposureCardinality.LocationCoherent tree after.1 protections ∧
    GeneralBorrowLocationSifaConsistency.Profile tree after.1 protections ∧
    GeneralBorrowSnapshotReadRuntime.GlobalPossible tree after.1 ∧
    Nonempty (GeneralBorrowFreshRootScopedRow.Row tree after.1 protections anchor selected selectedNode.tag)
  exact final
end DuplicatePrefix.GeneralBorrowFreshRootScopedAccess
