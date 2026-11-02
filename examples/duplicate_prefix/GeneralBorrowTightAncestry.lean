import duplicate_prefix.GeneralBorrowFreshReuseBudget
import duplicate_prefix.GeneralBorrowFreshAllocatorInvariant
namespace DuplicatePrefix.GeneralBorrowTightAncestry
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

noncomputable def chain (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) (index : UniIndex) : List UniIndex :=
  match present : nodes.get index with
  | none => []
  | some node => index :: (match edge : node.parent with
    | none => []
    | some parent => chain nodes depth parent)
termination_by depth.depth index
decreasing_by exact (depth.parent index node present parent edge).choose_spec.2

 theorem chain_present (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) (index : UniIndex) :
    ∀ query ∈ chain nodes depth index, ∃ node, nodes.get query = some node := by
  unfold chain
  split
  · simp
  · rename_i node present
    intro query member
    simp only [List.mem_cons] at member
    rcases member with same | member
    · subst query; exact ⟨node,present⟩
    · split at member
      · simp at member
      · rename_i parent edge
        exact chain_present nodes depth parent query member
termination_by depth.depth index
decreasing_by
  exact (depth.parent index _ (by assumption) _ (by assumption)).choose_spec.2

theorem chain_rank (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) (index : UniIndex) :
    ∀ query ∈ chain nodes depth index, depth.depth query ≤ depth.depth index := by
  unfold chain
  split
  · simp
  · rename_i node present
    intro query member
    simp only [List.mem_cons] at member
    rcases member with same | member
    · subst query; exact Nat.le_refl _
    · split at member
      · simp at member
      · rename_i parent edge
        have lower := (depth.parent index node present parent edge).choose_spec.2
        exact Nat.le_trans (chain_rank nodes depth parent query member) (Nat.le_of_lt lower)
termination_by depth.depth index
decreasing_by exact (depth.parent index _ (by assumption) _ (by assumption)).choose_spec.2

theorem chain_nodup (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) (index : UniIndex) :
    (chain nodes depth index).Nodup := by
  unfold chain
  split
  · simp
  · rename_i node present
    split
    · simp
    · rename_i parent edge
      apply List.nodup_cons.mpr
      refine ⟨?_,chain_nodup nodes depth parent⟩
      intro member
      have lower := (depth.parent index node present parent edge).choose_spec.2
      have bound := chain_rank nodes depth parent index member
      omega
termination_by depth.depth index
decreasing_by exact (depth.parent index _ (by assumption) _ (by assumption)).choose_spec.2


theorem positions_nodup (indices : List UniIndex) (nodup : indices.Nodup) :
    (indices.map UniIndex.toNat).Nodup := by
  exact nodup.map UniIndex.toNat (fun left right different same =>
    different (GeneralBorrowNodeUpdate.index_injective left right same))

def occupied (nodes : UniValMap TreeNode) : List Nat :=
  (List.range nodes.data.size).filter fun position => nodes.data[position]?.join.isSome

theorem chain_length_occupied (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) (index : UniIndex) :
    (chain nodes depth index).length ≤ (occupied nodes).length := by
  have mapped := positions_nodup (chain nodes depth index) (chain_nodup nodes depth index)
  have subset : (chain nodes depth index).map UniIndex.toNat ⊆ occupied nodes := by
    intro position member
    obtain ⟨query,queryMember,rfl⟩ := List.mem_map.mp member
    obtain ⟨node,present⟩ := chain_present nodes depth index query queryMember
    have valid := GeneralBorrowNodeUpdate.lookup_valid nodes query node present
    apply List.mem_filter.mpr
    refine ⟨List.mem_range.mpr valid,?_⟩
    unfold UniValMap.get at present
    cases lookup : nodes.data[query.toNat]? with
    | none => simp [lookup] at present
    | some state =>
      simp only [lookup] at present
      simp only [lookup,Option.join_some,present,Option.isSome_some]
  simpa only [List.length_map] using mapped.length_le_of_subset subset

theorem chain_length_table (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) (index : UniIndex) :
    (chain nodes depth index).length ≤ nodes.size := by
  have bound := List.length_filter_le (fun position => nodes.data[position]?.join.isSome) (List.range nodes.data.size)
  have earlier := chain_length_occupied nodes depth index
  simp only [List.length_range] at bound
  exact Nat.le_trans earlier bound

theorem chain_nonempty (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node) :
    0 < (chain nodes depth index).length := by
  rw [chain,present]
  simp

theorem chain_edge (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (index parent : UniIndex) (node : TreeNode) (present : nodes.get index = some node)
    (edge : node.parent = some parent) :
    chain nodes depth index = index :: chain nodes depth parent := by
  rw [chain,present]
  dsimp only
  rw [edge]

/-- Reconstruct ranks from the actual ancestor chain, forgetting arbitrary
padding in the old acyclicity witness. No additional graph or safety premise. -/
noncomputable def tight (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) : ParentDepth nodes where
  depth := fun index => (chain nodes depth index).length-1
  bounded := by
    intro index node present
    have bound := chain_length_table nodes depth index
    omega
  parent := by
    intro index node present parent edge
    obtain ⟨earlier,parentPresent,lower⟩ := depth.parent index node present parent edge
    refine ⟨earlier,parentPresent,?_⟩
    have positive := chain_nonempty nodes depth parent earlier parentPresent
    rw [chain_edge nodes depth index parent node present edge,List.length_cons]
    omega


theorem chain_pool_bound (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (index : UniIndex) (free : Array UniIndex)
    (pool : GeneralBorrowFreshAllocatorInvariant.Pool nodes free) :
    (chain nodes depth index).length + free.size ≤ nodes.size := by
  have combined : (chain nodes depth index ++ free.toList).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨chain_nodup nodes depth index,pool.nodup,?_⟩
    intro query member vacant freeMember same
    obtain ⟨node,present⟩ := chain_present nodes depth index query member
    have none := pool.vacant vacant (Array.mem_toList_iff.mp freeMember)
    rw [←same,present] at none
    cases none
  have mapped := positions_nodup _ combined
  have subset : (chain nodes depth index ++ free.toList).map UniIndex.toNat ⊆ List.range nodes.data.size := by
    intro position member
    obtain ⟨query,queryMember,rfl⟩ := List.mem_map.mp member
    apply List.mem_range.mpr
    rcases List.mem_append.mp queryMember with fromChain | fromPool
    · obtain ⟨node,present⟩ := chain_present nodes depth index query fromChain
      exact GeneralBorrowNodeUpdate.lookup_valid nodes query node present
    · exact pool.bounded query (Array.mem_toList_iff.mp fromPool)
  have bound := mapped.length_le_of_subset subset
  simpa only [List.length_map,List.length_append,Array.length_toList,List.length_range,UniValMap.size] using bound

theorem present_slack (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (parent : UniIndex) (node : TreeNode) (present : nodes.get parent = some node) :
    (tight nodes depth).depth parent < nodes.size := by
  have positive := chain_nonempty nodes depth parent node present
  have bound := chain_length_table nodes depth parent
  change (chain nodes depth parent).length-1 < nodes.size
  omega

/-- The actual number of distinct vacant free slots supplies a descendant-chain
budget after tightening ranks. No initial rank slack or operation success is
assumed; after consuming one free slot the child retains the residual budget. -/
theorem pool_budget (nodes : UniValMap TreeNode) (depth : ParentDepth nodes)
    (parent : UniIndex) (node : TreeNode) (present : nodes.get parent = some node)
    (free : Array UniIndex) (pool : GeneralBorrowFreshAllocatorInvariant.Pool nodes free) :
    GeneralBorrowFreshReuseBudget.Budget (tight nodes depth) parent (free.size+1) := by
  have positive := chain_nonempty nodes depth parent node present
  have bound := chain_pool_bound nodes depth parent free pool
  change (chain nodes depth parent).length-1 + (free.size+1) ≤ nodes.size
  omega

end DuplicatePrefix.GeneralBorrowTightAncestry
