import duplicate_prefix.GeneralBorrowGcForestComplete
import duplicate_prefix.GeneralBorrowGcOwnedPolicy
import duplicate_prefix.GeneralBorrowGcForestRootOwnership
import duplicate_prefix.GeneralBorrowParentlessTraversal

namespace DuplicatePrefix.GeneralBorrowGcRootWrite
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowAnchor DuplicatePrefix.GeneralBorrowPermissions
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowGcLocalEffectivePolicy
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private theorem allowed (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (present : tree.nodes.get root = some node) (parentless : node.parent = none)
    (query : UniIndex) (state : LocationState) (owned : GeneralBorrowGcOwnedPolicy.Allowed tree root .Write query state) :
    GeneralBorrowGcPartitionOwnership.Allowed root query state := by
  let location : LocationTree := ⟨⟨#[]⟩,{}⟩
  have valid : root.toNat < (source_normal_projection tree location {}).topology.nodes.size := by
    have bounded := GeneralBorrowNodeUpdate.lookup_valid tree.nodes root node present
    unfold_general_projection;unfold_general_topology
    simpa only [Array.size_map] using bounded
  have shape : (source_normal_projection tree location {}).topology.nodes[root.toNat] =
      ⟨node.parent.map UniIndex.toNat,node.children.toList.map UniIndex.toNat⟩ := by
    have shape := projection_topology_node tree location {} root.toNat root node rfl present
    simpa only [Array.getElem?_eq_getElem valid,Option.getD_some] using shape
  have noParent : (source_normal_projection tree location {}).topology.nodes[root.toNat].parent = none := by
    rw [shape,parentless];rfl
  have path := GeneralBorrowParentlessTraversal.ancestor_path (source_normal_projection tree location {}).topology root.toNat valid noParent
  have equal : query.toNat = root.toNat ↔ query = root :=
    ⟨GeneralBorrowNodeUpdate.index_injective query root,fun same => congrArg UniIndex.toNat same⟩
  change AccessOwned state .Write (relation (source_normal_projection tree location {}) root.toNat query.toNat) false at owned
  simp only [relation,path,List.mem_singleton,equal] at owned
  by_cases same : query = root
  · simpa only [GeneralBorrowGcPartitionOwnership.Allowed,same,ite_true,AccessOwned,Owned] using owned
  · simp only [same,ite_false,AccessOwned,Owned] at owned
    simpa only [GeneralBorrowGcPartitionOwnership.Allowed,same,ite_false] using owned.1

/-- Initial ownership at a genuine parentless root yields a graph-independent
range policy: only that root is local; every other source index is foreign. -/
theorem policy (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (present : tree.nodes.get root = some node) (parentless : node.parent = none)
    (lower upper : UInt64)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} root .Write) lower upper tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    Policy (GeneralBorrowGcPartitionOwnership.Allowed root) lower upper tree := by
  have initial := GeneralBorrowGcOwnedPolicy.of_owned tree root .Write lower upper owned clean
  refine ⟨?_,initial.vacant⟩
  intro query value found position valid positive before after
  exact allowed tree root node present parentless query _ (initial.live query value found position valid positive before after)

/-- FULL real arbitrary-forest GC retains Write ownership of any listed
parentless ROOT on any requested interval. Effective policy, real final Forest
and root survival are all derived; no surviving-child ancestry iff is needed
for this parentless anchor, and no post-GC ownership/success is a premise. -/
theorem collect (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (closed : GeneralBorrowGraph.ChildNodes tree) (fits : tree.nodes.size ≤ 4294967296)
    (rootNodes : ∀ root ∈ tree.roots.toList, ∃ node, tree.nodes.get root = some node ∧ node.parent = none)
    (well : tree.locations.WellFormed) (live : Array BorTag)
    (root : UniIndex) (node : TreeNode) (present : tree.nodes.get root = some node) (parentless : node.parent = none)
    (listed : root ∈ tree.roots.toList) (lower upper : UInt64)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} root .Write) lower upper tree.locations)
    (clean : GeneralBorrowGcVacantClean.VacantClean tree) :
    (tree.removeUnreachableTags live).outcome = .ok () ∧
    ∃ current, (tree.removeUnreachableTags live).tree.nodes.get root = some current ∧ current.parent = none ∧
      current.tag = node.tag ∧ OwnedOn (GeneralBorrowRange.LocationOwned (tree.removeUnreachableTags live).tree {} root .Write)
        lower upper (tree.removeUnreachableTags live).tree.locations := by
  obtain ⟨success,_,_,capacity,_,forests,_,_,metadata,roots⟩ := GeneralBorrowGcForestComplete.complete tree location protections forest depth closed fits rootNodes well live
  obtain ⟨current,currentPresent,currentParent⟩ := roots root listed
  obtain ⟨originalNode,originalPresent,fields⟩ := metadata root current currentPresent
  have equal := Option.some.inj (present.symm.trans originalPresent)
  subst originalNode
  have initialPolicy := policy tree root node present parentless lower upper owned clean
  have finalPolicy := GeneralBorrowGcLocalEffectivePolicy.preserves _ lower upper tree live initialPolicy
  have finalFits : (tree.removeUnreachableTags live).tree.nodes.size ≤ 4294967296 := by rw [capacity];exact fits
  have restored := GeneralBorrowGcForestRootOwnership.ownership (tree.removeUnreachableTags live).tree root current currentPresent currentParent
    (fun nextLocation => Classical.choice (forests nextLocation {})) lower upper finalPolicy finalFits
  exact ⟨success,current,currentPresent,currentParent,fields.tag,restored⟩

end
end DuplicatePrefix.GeneralBorrowGcRootWrite
