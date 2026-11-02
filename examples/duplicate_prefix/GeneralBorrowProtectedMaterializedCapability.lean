import duplicate_prefix.GeneralBorrowProtectedMaterializedNormal
namespace DuplicatePrefix.GeneralBorrowProtectedMaterializedCapability
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshChild GeneralBorrowFreshMaterialization
open GeneralBorrowProtectedNormalTables
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem topology_size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

/-- Exact raw extension data rebuild the fresh protected child Both Normal. -/
theorem from_extension (before after : BorrowTree) (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (parent child : UniIndex)
    (normal : DuplicatePrefixBorrowAuthorization.Normal before oldLocation protections parent)
    (extension : Extension (source_normal_projection before oldLocation protections)
      (source_normal_projection after newLocation protections) parent.toNat child.toNat) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal after newLocation protections child) := by
  have tables : ∀ kind, Table (source_normal_projection before oldLocation protections) parent.toNat kind normal.component.support := by
    intro kind index included valid
    exact normal.permissions kind index included (by rw [←topology_size before oldLocation protections];exact valid)
  obtain ⟨current,tablesAfter⟩ := certificate
    (source_normal_projection before oldLocation protections) (source_normal_projection after newLocation protections)
      parent.toNat child.toNat normal.component extension tables
  refine ⟨⟨current,?_⟩⟩
  intro kind index included valid
  exact tablesAfter kind index included (by rw [topology_size after newLocation protections];exact valid)

/-- Actual mutable append/materialization rebuilds the protected child Both Normal
capability from raw parent Normal, without old global permission profiles. -/
theorem append (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (present : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (heldTag : protections.contains tag = true)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections parent) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (child tag parent))
      (materialized location index inside) protections index) :=
  from_extension tree _ location _ protections parent index normal
    (GeneralBorrowProtectedMaterializedNormal.append tree index parent parentNode tag atEnd present location protections heldTag forest)

/-- Reusing a genuine vacant node slot gives the same fresh-child Both Normal capability after inside materialization. -/
theorem reuse (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (present : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (heldTag : protections.contains tag = true)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections parent) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (child tag parent))
      (materialized location index inside) protections index) :=
  from_extension tree _ location _ protections parent index normal
    (GeneralBorrowProtectedMaterializedNormal.reuse tree index parent parentNode tag bounded vacant fits present location protections heldTag forest)

end DuplicatePrefix.GeneralBorrowProtectedMaterializedCapability
