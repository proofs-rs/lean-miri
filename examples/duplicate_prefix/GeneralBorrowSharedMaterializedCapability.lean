import duplicate_prefix.GeneralBorrowSharedMaterializedNormal
namespace DuplicatePrefix.GeneralBorrowSharedMaterializedCapability
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowFreshAnchor GeneralBorrowFreshMaterialization
open GeneralBorrowSharedNormalTables
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem topology_size (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection
  unfold_general_topology
  simp only [Array.size_map]

/-- Exact raw extension data rebuild the original Both Normal and the new
source's Read-only normal certificate, with coupled actual components. -/
theorem from_extension (before after : BorrowTree) (oldLocation newLocation : LocationTree) (protections : ProtectedTags)
    (parent child : UniIndex)
    (normal : DuplicatePrefixBorrowAuthorization.Normal before oldLocation protections parent)
    (extension : Extension (source_normal_projection before oldLocation protections)
      (source_normal_projection after newLocation protections) parent.toNat child.toNat) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal after newLocation protections parent) ∧
    Nonempty (DuplicatePrefixNormalKind.Capability after newLocation protections child .Read) := by
  have tables : ∀ kind, Table (source_normal_projection before oldLocation protections) parent.toNat kind normal.component.support := by
    intro kind index included valid
    exact normal.permissions kind index included (by rw [←topology_size before oldLocation protections];exact valid)
  obtain ⟨original,shared,originalSupport,sharedSupport,both,read⟩ :=
    certificates (source_normal_projection before oldLocation protections) (source_normal_projection after newLocation protections)
      parent.toNat child.toNat normal.component extension tables
  refine ⟨⟨⟨original,?_⟩⟩,⟨⟨shared,?_⟩⟩⟩
  · intro kind index included valid
    exact both kind index included (by rw [topology_size after newLocation protections];exact valid)
  · intro index included valid
    exact read index included (by rw [topology_size after newLocation protections];exact valid)

/-- Actual shared append/materialization rebuilds both source-specific
capabilities from raw parent Normal, without old global permission profiles. -/
theorem append (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (atEnd : index.toNat = tree.nodes.data.size) (present : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (unprotected : protections.contains tag = false)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections parent) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode tag parent))
      (materialized location index sharedState) protections parent) ∧
    Nonempty (DuplicatePrefixNormalKind.Capability
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode tag parent))
      (materialized location index sharedState) protections index .Read) :=
  from_extension tree _ location _ protections parent index normal
    (GeneralBorrowSharedMaterializedNormal.append tree index parent parentNode tag atEnd present location protections unprotected forest)

/-- Reusing a genuine vacant node slot gives the same new-source Read and
old-source Both Normal capabilities after inside materialization. -/
theorem reuse (tree : BorrowTree) (index parent : UniIndex) (parentNode : TreeNode) (tag : BorTag)
    (bounded : index.toNat < tree.nodes.data.size) (vacant : tree.nodes.get index = none)
    (fits : tree.nodes.data.size ≤ 4294967296) (present : tree.nodeAt parent = some parentNode)
    (location : LocationTree) (protections : ProtectedTags) (unprotected : protections.contains tag = false)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (normal : DuplicatePrefixBorrowAuthorization.Normal tree location protections parent) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Normal
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode tag parent))
      (materialized location index sharedState) protections parent) ∧
    Nonempty (DuplicatePrefixNormalKind.Capability
      (GeneralBorrowFreshGraph.attached tree index parent parentNode (sharedNode tag parent))
      (materialized location index sharedState) protections index .Read) :=
  from_extension tree _ location _ protections parent index normal
    (GeneralBorrowSharedMaterializedNormal.reuse tree index parent parentNode tag bounded vacant fits present location protections unprotected forest)

end DuplicatePrefix.GeneralBorrowSharedMaterializedCapability
