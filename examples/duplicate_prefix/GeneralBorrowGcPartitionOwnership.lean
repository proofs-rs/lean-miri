import duplicate_prefix.GeneralBorrowGcEffectivePolicy
import duplicate_prefix.GeneralBorrowPartitionState

namespace DuplicatePrefix.GeneralBorrowGcPartitionOwnership
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowPermissions
open DuplicatePrefix.GeneralBorrowGcEffectivePolicy DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowAnchor
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def Allowed (root query : UniIndex) (state : LocationState) : Prop :=
  if query = root then LocalOwned state false else state.possible = true

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

/-- Initial root Write ownership supplies interval-dependent effective permission
constraints, including lazy shared/mutable defaults. -/
theorem of_state (tree : BorrowTree) (root : UniIndex) (bytes : UInt64)
    (s : GeneralBorrowPartitionState.State tree root bytes) : Policy (Allowed root) tree := by
  refine ⟨?_,s.clean⟩
  intro query node present position valid
  let location := tree.locations.entries[position].data
  have owner := (s.owned position valid).2
  have bound : query.toNat < (source_normal_projection tree location {}).topology.nodes.size := by
    rw [topology_size];exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes query node present
  obtain ⟨state,stored,permission⟩ := owner.permissions query.toNat bound
  have exactState := projection_state tree location {} query.toNat query node (index_self query) rfl present
  have equal : state = (location.perms.get query).getD node.defaultLocationState := Option.some.inj (stored.symm.trans exactState)
  subst state
  have rootPath := path tree root s.node location s.star.present s.star.parentless
  have related : relation (source_normal_projection tree location {}) root.toNat query.toNat =
      if query = root then .LocalAccess else .ForeignAccess := by
    simp only [relation,rootPath,List.mem_singleton]
    have iff : query.toNat = root.toNat ↔ query = root := ⟨GeneralBorrowNodeUpdate.index_injective query root,fun same => congrArg UniIndex.toNat same⟩
    simp only [iff]
  rw [related,unheld] at permission
  by_cases same : query = root
  · simpa only [Allowed,same,ite_true,AccessOwned,Owned] using permission
  · simp only [same,ite_false,AccessOwned,Owned] at permission
    simpa only [Allowed,same,ite_false,location] using permission.1

/-- Effective permissions and vacant Clean reconstruct actual root ownership
on every resulting GC interval; no homogeneous-profile premise is needed. -/
theorem ownership (tree : BorrowTree) (root : UniIndex) (node : TreeNode)
    (star : GeneralBorrowGeneratedStarShape.Star tree root node) (policy : Policy (Allowed root) tree)
    (fits : tree.nodes.size ≤ 4294967296) :
    Every (GeneralBorrowRange.LocationOwned tree {} root .Write) tree.locations := by
  change tree.nodes.data.size ≤ 4294967296 at fits
  intro position bounded
  let location := tree.locations.entries[position].data
  have rootPath := path tree root node location star.present star.parentless
  refine ⟨⟨GeneralBorrowStarCertificates.forest tree root node star location {} fits⟩,?_,?_,?_,?_⟩
  · rw [topology_size];exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes root node star.present
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
      have good := policy.live query value present position bounded
      rw [related,unheld]
      by_cases same : query = root
      · simpa only [Allowed,same,ite_true,AccessOwned,Owned,state,location] using good
      · simp only [Allowed,same,ite_false] at good
        simp only [same,ite_false,AccessOwned,Owned]
        exact ⟨good,Or.inl rfl⟩
    | none =>
      have clean := policy.vacant query present position bounded
      have notRoot : query ≠ root := by intro same;subst query;rw [star.present] at present;cases present
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

end DuplicatePrefix.GeneralBorrowGcPartitionOwnership
