import duplicate_prefix.GeneralBorrowFreshReborrowStages
import duplicate_prefix.GeneralBorrowFreshReuseNode
namespace DuplicatePrefix.GeneralBorrowFreshAllocatorInvariant
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- Initial sparse allocator coherence. Node vacancy does not assert absence of
per-location permissions; constructor clients must separately supply slot Clean.
Duplicate free indices are excluded because a consumed slot becomes occupied. -/
structure Pool (nodes : UniValMap TreeNode) (free : Array UniIndex) : Prop where
  bounded : ∀ index, index ∈ free → index.toNat < nodes.data.size
  vacant : ∀ index, index ∈ free → nodes.get index = none
  nodup : free.toList.Nodup

set_option autoImplicit false in
/-- Arbitrary-length free pools select the actual source allocator's back slot.
Strict rank slack is explicit: ParentDepth only gives a non-strict bound. -/
def slot (tree : BorrowTree) (depth : ParentDepth tree.nodes) (parent : UniIndex)
    (pool : Pool tree.nodes tree.tagMapping.deassigned)
    (aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (slack : depth.depth parent < tree.nodes.size) : Slot tree depth parent :=
  match available : tree.tagMapping.deassigned.back? with
  | none => .append available (aligned available) (fits available)
  | some index => .reuse index available
      (pool.bounded index (Array.mem_of_back? available))
      (pool.vacant index (Array.mem_of_back? available)) slack

set_option autoImplicit false in
/-- Consuming the actual back slot preserves coherence of every remaining free
slot after the new-node insertion. No claim about rank or permission data is
inferred from this allocator-only invariant. -/
theorem consume (nodes : UniValMap TreeNode) (free : Array UniIndex)
    (pool : Pool nodes free) (index : UniIndex) (available : free.back? = some index)
    (newNode : TreeNode) : Pool (nodes.insert index newNode) free.pop := by
  obtain ⟨rest,rfl⟩ := Array.back?_eq_some_iff.mp available
  have parts := List.nodup_append.mp (show (rest.toList ++ [index]).Nodup from by
    simpa only [Array.toList_push] using pool.nodup)
  have different : ∀ query, query ∈ rest → query ≠ index := by
    intro query member
    exact parts.2.2 query (Array.mem_toList_iff.mpr member) index (by simp)
  have indexBound := pool.bounded index (Array.mem_push_self (xs := rest) (x := index))
  have size := GeneralBorrowFreshReuseNode.bounded_size nodes index newNode indexBound
  simp only [Array.pop_push]
  refine ⟨?_,?_,parts.1⟩
  · intro query member
    have bound := pool.bounded query (Array.mem_push_of_mem index member)
    change query.toNat < (nodes.insert index newNode).size
    rw [size]
    exact bound
  · intro query member
    rw [GeneralBorrowFreshLocation.get_other nodes index query newNode (different query member)]
    exact pool.vacant query (Array.mem_push_of_mem index member)

set_option autoImplicit false in
/-- Updating a present parent's children cannot occupy any vacant free slot.
This complements consume for the second insertion performed by newChild. -/
theorem update_present (nodes : UniValMap TreeNode) (free : Array UniIndex)
    (pool : Pool nodes free) (parent : UniIndex) (oldNode newNode : TreeNode)
    (present : nodes.get parent = some oldNode) : Pool (nodes.insert parent newNode) free := by
  have size := GeneralBorrowNodeUpdate.insert_existing_size nodes parent oldNode newNode present
  refine ⟨?_,?_,pool.nodup⟩
  · intro query member
    change query.toNat < (nodes.insert parent newNode).size
    rw [size]
    exact pool.bounded query member
  · intro query member
    have different : query ≠ parent := by
      intro same
      subst query
      rw [pool.vacant parent member] at present
      cases present
    rw [GeneralBorrowFreshLocation.get_other nodes parent query newNode different]
    exact pool.vacant query member
set_option autoImplicit false in
/-- Both actual node insertions preserve the arbitrary residual free pool. -/
theorem attached (nodes : UniValMap TreeNode) (free : Array UniIndex)
    (pool : Pool nodes free) (index parent : UniIndex)
    (available : free.back? = some index) (parentNode newNode : TreeNode)
    (present : nodes.get parent = some parentNode) :
    Pool (GeneralBorrowFreshNode.attachedNodes nodes index parent parentNode newNode) free.pop := by
  have vacant := pool.vacant index (Array.mem_of_back? available)
  have different := GeneralBorrowFreshReuseNode.parent_not_vacant nodes index parent parentNode vacant present
  have parentAfter := (GeneralBorrowFreshLocation.get_other nodes index parent newNode different).trans present
  exact update_present (nodes.insert index newNode) free.pop (consume nodes free pool index available newNode)
    parent parentNode {parentNode with children := parentNode.children.push index} parentAfter

end DuplicatePrefix.GeneralBorrowFreshAllocatorInvariant
