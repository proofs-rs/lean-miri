import duplicate_prefix.GeneralBorrowWildcardForestWeights
import duplicate_prefix.GeneralBorrowWildcardSubtreeInvariant
import duplicate_prefix.DuplicatePrefixResidualSupportAuthorization
namespace DuplicatePrefix.GeneralBorrowWildcardControlStack
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowWildcardSubtreeData GeneralBorrowWildcardSubtreeStack
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Permission-free initial support data for the actual wildcard DFS. -/
structure Support (tree : BorrowTree) (root : UniIndex) where
  contains : UniIndex → Prop
  rooted : contains root
  present : ∀ index, contains index → ∃ node, tree.nodes.get index = some node
  children : ∀ index node, contains index → tree.nodes.get index = some node →
    ∀ child ∈ node.children.toList, contains child

structure Invariant {tree : BorrowTree} {root : UniIndex}
    (weights : Weights tree) (support : Support tree root) (stack : Array Task) (steps : Nat) : Prop where
  known : ∀ task ∈ stack.toList, support.contains task.1
  ranked : Ranked weights.weight stack
  budget : steps + potential weights.weight stack ≤ 2 * weights.weight root

def Support.of_authorization (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (root : UniIndex) (position : Nat) (maximum : Option BorTag) (kind : AccessKind) (set : UniIndex → Prop)
    (authorized : DuplicatePrefixResidualSupportAuthorization.Authorization tree location protections root position maximum kind set) : Support tree root :=
  ⟨set,authorized.rooted,authorized.present,authorized.children⟩

theorem initial {tree : BorrowTree} {root : UniIndex} (weights : Weights tree) (support : Support tree root) :
    Invariant weights support #[(root,false)] 0 := by
  refine ⟨?_,?_,?_⟩
  · intro task member
    have same : task = (root,false) := by simpa using member
    subst task
    exact support.rooted
  · simp [Ranked]
  · simp [potential,cost]

/-- The real nonempty source stack cannot name a missing node. -/
theorem top_present {tree : BorrowTree} {root : UniIndex} (weights : Weights tree) (support : Support tree root)
    (stack : Array Task) (index : UniIndex) (post : Bool) (steps : Nat)
    (valid : Invariant weights support (stack.push (index,post)) steps) :
    ∃ node, tree.nodes.get index = some node :=
  support.present index (valid.known (index,post) (by simp))

/-- The pinned source's steps+1 > size*2+1 cycle branch is false. -/
theorem not_past {tree : BorrowTree} {root : UniIndex} (weights : Weights tree) (support : Support tree root)
    (stack : Array Task) (steps : Nat) (valid : Invariant weights support stack steps)
    (bounded : weights.weight root ≤ tree.nodes.size) : ¬steps+1 > tree.nodes.size*2+1 := by
  have budget := valid.budget
  omega

theorem pop {tree : BorrowTree} {root : UniIndex} (weights : Weights tree) (support : Support tree root)
    (stack : Array Task) (task : Task) (steps : Nat)
    (valid : Invariant weights support (stack.push task) steps) :
    Invariant weights support stack (steps+1) := by
  obtain ⟨node,present⟩ := support.present task.1 (valid.known task (by simp))
  have positive : 1 ≤ cost weights.weight task := by
    have bounded := weights.children task.1 node present
    cases task with | mk index post => cases post <;> simp [cost] <;> dsimp only at bounded ⊢ <;> omega
  refine ⟨?_,((ranked_push weights.weight stack task).mp valid.ranked).1,?_⟩
  · intro next member
    exact valid.known next (by simp [member])
  · have old := valid.budget
    rw [potential_push] at old
    omega

theorem expand {tree : BorrowTree} {root : UniIndex} (weights : Weights tree) (support : Support tree root)
    (stack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant weights support (stack.push (index,false)) steps)
    (present : tree.nodes.get index = some node) :
    Invariant weights support (expanded stack index node.children) (steps+1) := by
  have contained := valid.known (index,false) (by simp)
  refine ⟨?_,expanded_ranked weights.weight stack index node.children valid.ranked
    (GeneralBorrowWildcardSubtreeInvariant.child_smaller weights index node present),?_⟩
  · intro task member
    simp only [expanded,Array.toList_append,Array.toList_push,Array.toList_map,List.mem_append] at member
    rcases member with old | inChildren
    · rcases old with earlier | current
      · exact valid.known task (by simp [earlier])
      · have same : task = (index,true) := by simpa using current
        subst task
        exact contained
    · obtain ⟨childIndex,childMember,same⟩ := List.mem_map.mp inChildren
      subst task
      exact support.children index node contained present childIndex childMember
  · have old := valid.budget
    rw [potential_push] at old
    simp only [cost,Bool.false_eq_true,ite_false] at old
    rw [expanded_potential]
    have bounded := weights.children index node present
    omega

/-- A pending postvisit has strictly larger rank than every task above it.
Thus writing a completed descendant cannot change that pending parent's row. -/
theorem pending_different {tree : BorrowTree} {root : UniIndex} (weights : Weights tree) (support : Support tree root)
    (stack : Array Task) (index : UniIndex) (post : Bool) (steps : Nat)
    (valid : Invariant weights support (stack.push (index,post)) steps)
    (parent : UniIndex) (pending : (parent,true) ∈ stack.toList) : parent ≠ index := by
  have smaller := ((ranked_push weights.weight stack (index,post)).mp valid.ranked).2 (parent,true) pending rfl
  intro same
  subst parent
  exact Nat.lt_irrefl _ smaller

end DuplicatePrefix.GeneralBorrowWildcardControlStack
