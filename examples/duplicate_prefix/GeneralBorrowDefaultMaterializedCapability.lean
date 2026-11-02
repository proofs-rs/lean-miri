import duplicate_prefix.GeneralBorrowDefaultMaterializedNormal
namespace DuplicatePrefix.GeneralBorrowDefaultMaterializedCapability
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshDefaultChild GeneralBorrowFreshMaterialization
open GeneralBorrowDefaultNormalTables
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem topology_size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

/-- Exact raw extension data rebuild the original Both Normal and the new
source's Both Normal certificate, with coupled actual components. -/
theorem from_extension (before after : BorrowTree) (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (parent child : UniIndex)
    (normal : DuplicatePrefixBorrowAuthorization.Normal before oldLocation protections parent)
    (extension : Extension (source_normal_projection before oldLocation protections)
      (source_normal_projection after newLocation protections) parent.toNat child.toNat) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal after newLocation protections parent) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal after newLocation protections child) := by
  have tables : ∀ kind, Table (source_normal_projection before oldLocation protections) parent.toNat kind normal.component.support := by
    intro kind index included valid
    exact normal.permissions kind index included (by rw [←topology_size before oldLocation protections];exact valid)
  obtain ⟨original,shared,originalSupport,sharedSupport,both,read⟩ :=
    certificates (source_normal_projection before oldLocation protections) (source_normal_projection after newLocation protections)
      parent.toNat child.toNat normal.component extension tables
  refine ⟨⟨⟨original,?_⟩⟩,⟨⟨shared,?_⟩⟩⟩
  · intro kind index included valid
    exact both kind index included (by rw [topology_size after newLocation protections];exact valid)
  · intro kind index included valid
    exact read kind index included (by rw [topology_size after newLocation protections];exact valid)

/-- Actual mutable append/materialization rebuilds both source-specific
capabilities from raw parent Normal, without old global permission profiles. -/
theorem append (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (present : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (unprotected : protections.contains tag = false)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections parent) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (child tag parent))
      (materialized location index inside) protections parent) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (child tag parent))
      (materialized location index inside) protections index) :=
  from_extension tree _ location _ protections parent index normal
    (GeneralBorrowDefaultMaterializedNormal.append tree index parent parentNode tag atEnd present location protections unprotected forest)

/-- Reusing a genuine vacant node slot gives the same new-source Both and
old-source Both Normal capabilities after inside materialization. -/
theorem reuse (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (present : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (unprotected : protections.contains tag = false)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections parent) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (child tag parent))
      (materialized location index inside) protections parent) ∧
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (child tag parent))
      (materialized location index inside) protections index) :=
  from_extension tree _ location _ protections parent index normal
    (GeneralBorrowDefaultMaterializedNormal.reuse tree index parent parentNode tag bounded vacant fits present location protections unprotected forest)

end DuplicatePrefix.GeneralBorrowDefaultMaterializedCapability
