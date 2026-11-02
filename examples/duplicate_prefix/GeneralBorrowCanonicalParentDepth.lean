import duplicate_prefix.GeneralBorrowFreshAllocatorInvariant

namespace DuplicatePrefix.GeneralBorrowCanonicalParentDepth
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Enumeration uses the actual sparse-table positions; only present nodes
with a strictly smaller input rank contribute to the compressed rank. -/
def indexAt (position : Nat) : UniIndex := ⟨UInt32.ofNat position⟩

def lower (nodes : UniValMap TreeNode) (rank : UniIndex → Nat) (index : UniIndex) : List Nat :=
  (List.range nodes.size).filter fun position => (nodes.get (indexAt position)).isSome && decide (rank (indexAt position) < rank index)

private theorem at_self (index : UniIndex) : indexAt index.toNat = index := by
  cases index with
  | mk index => simp [indexAt,UniIndex.toNat]

private theorem mem_lower (nodes : UniValMap TreeNode) (rank : UniIndex → Nat) (index : UniIndex) (position : Nat) :
    position ∈ lower nodes rank index ↔ position < nodes.size ∧
      (nodes.get (indexAt position)).isSome = true ∧ rank (indexAt position) < rank index := by
  simp [lower,List.mem_filter,Bool.and_eq_true,decide_eq_true_eq]

private theorem finite_strict {left right : List Nat} (distinct : left.Nodup) (subset : left ⊆ right)
    (witness : Nat) (inside : witness ∈ right) (outside : witness ∉ left) : left.length < right.length := by
  have moreDistinct : (left ++ [witness]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨distinct,by simp,?_⟩
    intro query member other singleton same
    have equal : other = witness := by simpa only [List.mem_singleton] using singleton
    exact outside (same.trans equal ▸ member)
  have moreSubset : left ++ [witness] ⊆ right := by
    intro query member
    rcases List.mem_append.mp member with earlier | last
    · exact subset earlier
    · have equal : query = witness := by simpa only [List.mem_singleton] using last
      exact equal ▸ inside
  have count := moreDistinct.length_le_of_subset moreSubset
  simp only [List.length_append,List.length_singleton] at count
  omega

/-- Present nodes always have strict storage slack under the compressed rank,
regardless of the magnitude or gaps of the supplied ranking. -/
theorem strict (nodes : UniValMap TreeNode) (rank : UniIndex → Nat) (index : UniIndex) (node : TreeNode)
    (present : nodes.get index = some node) : (lower nodes rank index).length < nodes.size := by
  have distinct : (lower nodes rank index).Nodup := (List.nodup_range).filter _
  have subset : lower nodes rank index ⊆ List.range nodes.size := by
    intro position member
    exact List.mem_range.mpr ((mem_lower nodes rank index position).mp member).1
  have bound := DuplicatePrefix.GeneralBorrowNodeUpdate.lookup_valid nodes index node present
  have excluded : index.toNat ∉ lower nodes rank index := by
    intro included
    have impossible := ((mem_lower nodes rank index index.toNat).mp included).2.2
    rw [at_self] at impossible
    omega
  have count := finite_strict distinct subset index.toNat (List.mem_range.mpr bound) excluded
  simpa only [List.length_range] using count

/-- A parent edge remains strictly ranked after compression. Presence of the
parent provides the concrete extra member; no original rank-size bound is used. -/
theorem edge (nodes : UniValMap TreeNode) (rank : UniIndex → Nat) (parent child : UniIndex)
    (node : TreeNode) (present : nodes.get parent = some node) (increasing : rank parent < rank child) :
    (lower nodes rank parent).length < (lower nodes rank child).length := by
  have distinct : (lower nodes rank parent).Nodup := (List.nodup_range).filter _
  have subset : lower nodes rank parent ⊆ lower nodes rank child := by
    intro position included
    have facts := (mem_lower nodes rank parent position).mp included
    exact (mem_lower nodes rank child position).mpr ⟨facts.1,facts.2.1,Nat.lt_trans facts.2.2 increasing⟩
  have bound := DuplicatePrefix.GeneralBorrowNodeUpdate.lookup_valid nodes parent node present
  have inside : parent.toNat ∈ lower nodes rank child := by
    apply (mem_lower nodes rank child parent.toNat).mpr
    rw [at_self,present]
    exact ⟨bound,rfl,increasing⟩
  have outside : parent.toNat ∉ lower nodes rank parent := by
    intro included
    have impossible := ((mem_lower nodes rank parent parent.toNat).mp included).2.2
    rw [at_self] at impossible
    omega
  exact finite_strict distinct subset parent.toNat inside outside

/-- Canonical strict ParentDepth for any finite sparse ranked borrowing graph.
Only proof data is recomputed; source nodes, tree semantics and allocator state
are untouched. The supplied parent relation already excludes dangling cycles. -/
def normalize (nodes : UniValMap TreeNode) (before : ParentDepth nodes) : ParentDepth nodes where
  depth := fun index => (lower nodes before.depth index).length
  bounded := fun index node present => Nat.le_of_lt (strict nodes before.depth index node present)
  parent := by
    intro child node present parent parentEdge
    obtain ⟨earlier,parentPresent,increasing⟩ := before.parent child node present parent parentEdge
    exact ⟨earlier,parentPresent,edge nodes before.depth parent child earlier parentPresent increasing⟩

/-- Every present parent now satisfies the strict reuse precondition, including
parents arbitrarily deep below the root. -/
theorem slack (nodes : UniValMap TreeNode) (before : ParentDepth nodes) (parent : UniIndex) (node : TreeNode)
    (present : nodes.get parent = some node) : (normalize nodes before).depth parent < nodes.size :=
  strict nodes before.depth parent node present

/-- Actual source allocator selection from arbitrary coherent sparse free pools
requires no externally supplied rank slack once the graph has ParentDepth. -/
def slot (tree : BorrowTree) (before : ParentDepth tree.nodes) (parent : UniIndex) (node : TreeNode)
    (present : tree.nodeAt parent = some node)
    (pool : GeneralBorrowFreshAllocatorInvariant.Pool tree.nodes tree.tagMapping.deassigned)
    (aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295) :
    GeneralBorrowFreshReborrowStages.Slot tree (normalize tree.nodes before) parent :=
  GeneralBorrowFreshAllocatorInvariant.slot tree (normalize tree.nodes before) parent pool aligned fits (slack tree.nodes before parent node present)

end DuplicatePrefix.GeneralBorrowCanonicalParentDepth
