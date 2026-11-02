import duplicate_prefix.GeneralBorrowGcLocalEffectivePolicy
import duplicate_prefix.GeneralBorrowGcPartitionOwnership
namespace DuplicatePrefix.GeneralBorrowGcForestRootOwnership
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowPermissions
open DuplicatePrefix.GeneralBorrowGcPartitionOwnership DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowAnchor DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
private theorem path (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (location : LocationTree)
    (present : tree.nodeAt root = some node) (parentless : node.parent = none) :
    (source_normal_projection tree location {}).topology.ancestorPath root.toNat = [root.toNat] := by
  have parent : (GeneralBorrowPresence.nodeData (source_normal_projection tree location {}).topology root.toNat).parent = none := by
    change ((source_normal_projection tree location {}).topology.nodes[root.toNat]?.getD ⟨none,[]⟩).parent = none
    rw [projection_topology_node tree location {} root.toNat root node rfl present]
    simp only [parentless,Option.map_none]
  change sourceAncestorPath (source_normal_projection tree location {}).topology
    (source_normal_projection tree location {}).topology.nodes.size root.toNat = _
  cases (source_normal_projection tree location {}).topology.nodes.size with
  | zero => rfl
  | succ fuel => rw [GeneralBorrowPresence.ancestor_succ,parent]

private theorem topology_size (tree : BorrowTree) (location : LocationTree) :
    (source_normal_projection tree location {}).topology.nodes.size = tree.nodes.data.size := by
  unfold_general_projection;unfold_general_topology;simp only [Array.size_map]

private theorem unheld (tree : BorrowTree) (location : LocationTree) (position : Nat) :
    (source_normal_projection tree location {}).protectedNodes.contains position = false := by
  have empty : (source_normal_projection tree location {}).protectedNodes = [] := by
    unfold_general_projection;simp [ProtectedTags.contains,ProtectedTags.get]
  rw [empty];rfl

/-- A parentless surviving root, an actual final forest, and the retained
range-local effective policy reconstruct root Write ownership. Structural
certificates remain explicit here; no GC-success claim is inferred from them. -/
theorem ownership (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (rootPresent : tree.nodeAt root = some node) (parentless : node.parent = none)
    (forest : ∀ location : LocationTree, GeneralBorrowForest.Forest (source_normal_projection tree location {}).topology)
    (lower upper : UInt64) (policy : GeneralBorrowGcLocalEffectivePolicy.Policy (Allowed root) lower upper tree)
    (fits : tree.nodes.size ≤ 4294967296) :
    OwnedOn (GeneralBorrowRange.LocationOwned tree {} root .Write) lower upper tree.locations := by
  change tree.nodes.data.size ≤ 4294967296 at fits
  intro position bounded positive beforeUpper afterLower
  let location := tree.locations.entries[position].data
  have rootPath := path tree root node location rootPresent parentless
  refine ⟨⟨forest location⟩,?_,?_,?_,?_⟩
  · rw [topology_size];exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes root node rootPresent
  · exact (projection_sizes tree location {}).1.trans (topology_size tree location).symm
  · exact (projection_sizes tree location {}).2.trans (topology_size tree location).symm
  · intro index valid
    have bound : index < tree.nodes.data.size := by rw [←topology_size tree location];exact valid
    obtain ⟨query,converted,equal⟩ := index_nat index (by omega)
    have related : relation (source_normal_projection tree location {}) root.toNat index =
        if query = root then .LocalAccess else .ForeignAccess := by
      simp only [relation,rootPath,List.mem_singleton]
      have iff : index = root.toNat ↔ query = root :=
        ⟨fun same => GeneralBorrowNodeUpdate.index_injective query root (equal.trans same),fun same => equal.symm.trans (congrArg UniIndex.toNat same)⟩
      simp only [iff]
    cases present : tree.nodeAt query with
    | some value =>
      let state := (location.perms.get query).getD value.defaultLocationState
      refine ⟨state,projection_state tree location {} index query value converted equal present,?_⟩
      have good := policy.live query value present position bounded positive beforeUpper afterLower
      rw [related,unheld]
      by_cases same : query = root
      · simpa only [Allowed,same,ite_true,AccessOwned,Owned,state,location] using good
      · simp only [Allowed,same,ite_false] at good
        simp only [same,ite_false,AccessOwned,Owned]
        exact ⟨good,Or.inl rfl⟩
    | none =>
      have clean := policy.vacant query present position bounded
      have notRoot : query ≠ root := by intro same;subst query;rw [rootPresent] at present;cases present
      refine ⟨⟨.Disabled,false,.None⟩,?_,?_⟩
      · unfold_general_projection
        unfold NormalTreeState.stateAt
        simp only [Array.getElem?_mapIdx,converted,clean,Array.getElem?_map,
          Array.getElem?_eq_getElem bound,Option.map_some,Option.getD_some]
        have absent : tree.nodes.data[index] = none := by
          unfold BorrowTree.nodeAt UniValMap.get at present
          rw [equal,Array.getElem?_eq_getElem bound] at present
          exact present
        simp only [absent]
      · rw [related,ite_eq_right notRoot,unheld]
        exact ⟨rfl,Or.inl rfl⟩

end DuplicatePrefix.GeneralBorrowGcForestRootOwnership
