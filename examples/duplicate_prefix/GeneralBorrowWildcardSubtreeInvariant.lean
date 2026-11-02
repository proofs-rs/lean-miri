import duplicate_prefix.GeneralBorrowWildcardSubtreeStack
import duplicate_prefix.GeneralBorrowWildcardSubtreeState

namespace DuplicatePrefix.GeneralBorrowWildcardSubtreeInvariant
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowWildcardSubtreeData GeneralBorrowWildcardSubtreeStack GeneralBorrowWildcardSubtreeState
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
abbrev LoopState := LocationTree × Bool × BorrowTree.WildcardAccessStatus × Array Task × Nat

def Pending (tree : BorrowTree) (kind : AccessKind) (location : LocationTree) (stack : Array Task) : Prop :=
  ∀ index node, (index,true) ∈ stack.toList → tree.nodes.get index = some node →
    (effective location index node).skipIfKnownNoop kind .ForeignAccess = .Recurse

structure Invariant {tree : BorrowTree} {initial : LocationTree} {root : UniIndex}
    {kind : AccessKind} {protections : ProtectedTags} (weights : Weights tree)
    (data : Data tree initial root kind protections) (state : LoopState) : Prop where
  status : state.2.2.1 = .Completed
  witness : state.2.1 = false
  cache : state.1.exposedCache = initial.exposedCache
  owned : Owned data state.1
  pending : Pending tree kind state.1 state.2.2.2.1
  known : ∀ task ∈ state.2.2.2.1.toList, data.support task.1
  ranked : Ranked weights.weight state.2.2.2.1
  budget : state.2.2.2.2 + potential weights.weight state.2.2.2.1 ≤ 2 * weights.weight root
  outside : ∀ query, ¬data.support query → state.1.perms.get query = initial.perms.get query

theorem initial {tree : BorrowTree} {location : LocationTree} {root : UniIndex}
    {kind : AccessKind} {protections : ProtectedTags} (weights : Weights tree)
    (data : Data tree location root kind protections) :
    Invariant weights data (location,false,.Completed,#[(root,false)],0) := by
  refine ⟨rfl,rfl,rfl,data.owned,?_,?_,?_,?_,fun _ _ => rfl⟩
  · intro index node member present
    simp at member
  · intro task member
    have same : task = (root,false) := by simpa using member
    subst task
    exact data.root
  · simp [Ranked]
  · simp [potential,cost]

theorem member_le_sum (weight : UniIndex → Nat) (items : List UniIndex) (child : UniIndex)
    (member : child ∈ items) : weight child ≤ (items.map weight).sum := by
  induction items with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with same | later
    · subst child
      simp
    · have bound := ih later
      simp only [List.map_cons,List.sum_cons]
      omega

theorem child_smaller {tree : BorrowTree} (weights : Weights tree) (index : UniIndex) (node : TreeNode)
    (present : tree.nodes.get index = some node) (child : UniIndex) (member : child ∈ node.children.toList) :
    weights.weight child < weights.weight index := by
  have bounded := weights.children index node present
  have included := member_le_sum weights.weight node.children.toList child member
  omega

/-- Dropping a completed/skipped top task preserves all stack-data invariants;
the caller supplies only its source-independent positive-cost bound. -/
theorem pop {tree : BorrowTree} {initial : LocationTree} {root : UniIndex}
    {kind : AccessKind} {protections : ProtectedTags} (weights : Weights tree)
    (data : Data tree initial root kind protections) (location : LocationTree)
    (baseStack : Array Task) (task : Task) (steps : Nat)
    (valid : Invariant weights data (location,false,.Completed,baseStack.push task,steps))
    (positive : 1 ≤ cost weights.weight task) :
    Invariant weights data (location,false,.Completed,baseStack,steps+1) := by
  refine ⟨rfl,rfl,valid.cache,valid.owned,?_,?_,?_,?_,valid.outside⟩
  · intro index node member present
    exact valid.pending index node (by simp [member]) present
  · intro item member
    exact valid.known item (by simp [member])
  · exact ((ranked_push weights.weight baseStack task).mp valid.ranked).1
  · have old := valid.budget
    dsimp only at old ⊢
    rw [potential_push] at old
    omega

theorem expand {tree : BorrowTree} {initial : LocationTree} {root : UniIndex}
    {kind : AccessKind} {protections : ProtectedTags} (weights : Weights tree)
    (data : Data tree initial root kind protections) (location : LocationTree)
    (baseStack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant weights data (location,false,.Completed,baseStack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (recurse : (effective location index node).skipIfKnownNoop kind .ForeignAccess = .Recurse) :
    Invariant weights data (location,false,.Completed,expanded baseStack index node.children,steps+1) := by
  have supported : data.support index := valid.known (index,false) (by simp)
  refine ⟨rfl,rfl,valid.cache,valid.owned,?_,?_,?_,?_,valid.outside⟩
  · intro query queryNode member queryPresent
    simp only [expanded,Array.toList_append,Array.toList_push,Array.toList_map,List.mem_append] at member
    rcases member with old | child
    · rcases old with earlier | current
      · exact valid.pending query queryNode (by simp [earlier]) queryPresent
      · have same : query = index := by simpa using current
        subst query
        have nodeEq := Option.some.inj (present.symm.trans queryPresent)
        subst queryNode
        exact recurse
    · obtain ⟨child,childMember,impossible⟩ := List.mem_map.mp child
      simp at impossible
  · intro task member
    simp only [expanded,Array.toList_append,Array.toList_push,Array.toList_map,List.mem_append] at member
    rcases member with old | child
    · rcases old with earlier | current
      · exact valid.known task (by simp [earlier])
      · have same : task = (index,true) := by simpa using current
        subst task
        exact supported
    · obtain ⟨childIndex,childMember,eq⟩ := List.mem_map.mp child
      subst task
      exact data.children index node supported present childIndex childMember
  · exact expanded_ranked weights.weight baseStack index node.children valid.ranked
      (child_smaller weights index node present)
  · have previous := valid.budget
    dsimp only at previous ⊢
    rw [potential_push] at previous
    simp only [cost,Bool.false_eq_true,↓reduceIte] at previous
    rw [expanded_potential]
    have childrenBound := weights.children index node present
    omega

theorem post {tree : BorrowTree} {initial : LocationTree} {root : UniIndex}
    {kind : AccessKind} {protections : ProtectedTags} (weights : Weights tree)
    (data : Data tree initial root kind protections) (location : LocationTree)
    (baseStack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (recorded next : LocationState)
    (valid : Invariant weights data (location,false,.Completed,baseStack.push (index,true),steps))
    (present : tree.nodes.get index = some node)
    (newOwned : GeneralBorrowPermissions.ForeignOwned next (protections.contains node.tag)) :
    Invariant weights data (write location index node recorded next,false,.Completed,baseStack,steps+1) := by
  have supported : data.support index := valid.known (index,true) (by simp)
  obtain ⟨rankedPrefix,before⟩ := (ranked_push weights.weight baseStack (index,true)).mp valid.ranked
  refine ⟨rfl,rfl,?_,owned_write data location index node recorded next present valid.owned newOwned,?_,?_,rankedPrefix,?_,?_⟩
  · dsimp only [write]
    exact valid.cache
  · intro query queryNode member queryPresent
    have smaller := before (query,true) member rfl
    have different : query ≠ index := by intro same; subst query; exact Nat.lt_irrefl _ smaller
    simpa only [effective,write_other location index query node recorded next different] using
      valid.pending query queryNode (by simp [member]) queryPresent
  · intro task member
    exact valid.known task (by simp [member])
  · have previous := valid.budget
    dsimp only at previous ⊢
    rw [potential_push] at previous
    simp only [cost,↓reduceIte] at previous
    omega
  · intro query outside
    have different : query ≠ index := by intro same; subst query; exact outside supported
    exact (write_other location index query node recorded next different).trans (valid.outside query outside)

end DuplicatePrefix.GeneralBorrowWildcardSubtreeInvariant
