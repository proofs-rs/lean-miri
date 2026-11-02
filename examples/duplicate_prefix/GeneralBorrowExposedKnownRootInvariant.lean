import duplicate_prefix.GeneralBorrowExposedKnownRootState

namespace DuplicatePrefix.GeneralBorrowExposedKnownRootInvariant
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective materialized)
open GeneralBorrowWildcardSubtreeData (Weights)
open GeneralBorrowWildcardSubtreeStack
open GeneralBorrowExposedNonleafState (ReadFrame foreign)
open GeneralBorrowExposedKnownRootState
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]

set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
abbrev LoopState := LocationTree × Bool × BorrowTree.WildcardAccessStatus × Array Task × Nat

def Pending (tree : BorrowTree) (initial current : LocationTree) (maximum : Option Miri.Memory.BorTag)
    (stack : Array Task) : Prop :=
  ∀ index node, (index,true) ∈ stack.toList → tree.nodes.get index = some node →
    foreign initial index node maximum = true → (effective current index node).skipIfKnownNoop .Read .ForeignAccess = .Recurse

structure Invariant {tree initial root protections} (weights : Weights tree)
    (data : Data tree initial root protections) (maximum : Option Miri.Memory.BorTag) (state : LoopState) : Prop where
  status : state.2.2.1 = .Completed
  frame : ReadFrame initial state.1
  readable : Readable tree state.1 protections
  pending : Pending tree initial state.1 maximum state.2.2.2.1
  known : ∀ task ∈ state.2.2.2.1.toList, data.support task.1
  ranked : Ranked weights.weight state.2.2.2.1
  budget : state.2.2.2.2 + potential weights.weight state.2.2.2.1 ≤ 2 * weights.weight root
  coherent : GeneralBorrowExposureCardinality.LocationCoherent tree state.1 protections

theorem initial_from {tree location root protections} (weights : Weights tree)
    (data : Data tree location root protections) (maximum : Option Miri.Memory.BorTag) (current : LocationTree)
    (frame : ReadFrame location current) (readable : Readable tree current protections)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree current protections) :
    Invariant weights data maximum (current,false,.Completed,#[(root,false)],0) := by
  refine ⟨rfl,frame,readable,?_,?_,?_,?_,coherent⟩
  · intro index node member
    simp at member
  · intro task member
    have same : task = (root,false) := by simpa using member
    subst task
    exact data.rooted
  · simp [Ranked]
  · simp [potential,cost]

theorem initial {tree location root protections} (weights : Weights tree)
    (data : Data tree location root protections) (maximum : Option Miri.Memory.BorTag) :
    Invariant weights data maximum (location,false,.Completed,#[(root,false)],0) := by
  refine ⟨rfl,fun _ => rfl,data.readable,?_,?_,?_,?_,data.coherent⟩
  · intro index node member
    simp at member
  · intro task member
    have same : task = (root,false) := by simpa using member
    subst task
    exact data.rooted
  · simp [Ranked]
  · simp [potential,cost]

theorem pop {tree initial root protections} (weights : Weights tree) (data : Data tree initial root protections)
    (maximum : Option Miri.Memory.BorTag) (location : LocationTree) (witness : Bool)
    (baseStack : Array Task) (task : Task) (steps : Nat)
    (valid : Invariant weights data maximum (location,witness,.Completed,baseStack.push task,steps))
    (positive : 1 ≤ cost weights.weight task) :
    Invariant weights data maximum (location,witness,.Completed,baseStack,steps+1) := by
  refine ⟨rfl,valid.frame,valid.readable,?_,?_,((ranked_push weights.weight baseStack task).mp valid.ranked).1,?_,valid.coherent⟩
  · intro index node member present clamp
    exact valid.pending index node (by simp [member]) present clamp
  · intro item member
    exact valid.known item (by simp [member])
  · have old := valid.budget
    dsimp only at old ⊢
    rw [potential_push] at old
    omega

theorem expand {tree initial root protections} (weights : Weights tree) (data : Data tree initial root protections)
    (maximum : Option Miri.Memory.BorTag) (location : LocationTree) (witness : Bool)
    (baseStack : Array Task) (index : UniIndex) (node : TreeNode) (steps : Nat)
    (valid : Invariant weights data maximum (location,witness,.Completed,baseStack.push (index,false),steps))
    (present : tree.nodes.get index = some node)
    (recurse : foreign initial index node maximum = true → (effective location index node).skipIfKnownNoop .Read .ForeignAccess = .Recurse) :
    Invariant weights data maximum (location,witness,.Completed,expanded baseStack index node.children,steps+1) := by
  have supported : data.support index := valid.known (index,false) (by simp)
  refine ⟨rfl,valid.frame,valid.readable,?_,?_,?_,?_,valid.coherent⟩
  · intro query queryNode member queryPresent clamp
    simp only [expanded,Array.toList_append,Array.toList_push,Array.toList_map,List.mem_append] at member
    rcases member with old | child
    · rcases old with earlier | current
      · exact valid.pending query queryNode (by simp [earlier]) queryPresent clamp
      · have same : query = index := by simpa using current
        subst query
        have nodeEq := Option.some.inj (present.symm.trans queryPresent)
        subst queryNode
        exact recurse clamp
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
      (GeneralBorrowWildcardSubtreeInvariant.child_smaller weights index node present)
  · have previous := valid.budget
    dsimp only at previous ⊢
    rw [potential_push] at previous
    simp only [cost,Bool.false_eq_true,↓reduceIte] at previous
    rw [expanded_potential]
    have childrenBound := weights.children index node present
    omega

theorem post {tree initial root protections} (weights : Weights tree) (data : Data tree initial root protections)
    (maximum : Option Miri.Memory.BorTag) (location after : LocationTree) (witness afterWitness : Bool)
    (baseStack : Array Task) (index : UniIndex) (steps : Nat)
    (valid : Invariant weights data maximum (location,witness,.Completed,baseStack.push (index,true),steps))
    (frame : ReadFrame location after) (readable : Readable tree after protections)
    (unchanged : ∀ query, query ≠ index → after.perms.get query = location.perms.get query)
    (coherent : GeneralBorrowExposureCardinality.LocationCoherent tree after protections) :
    Invariant weights data maximum (after,afterWitness,.Completed,baseStack,steps+1) := by
  obtain ⟨rankedPrefix,before⟩ := (ranked_push weights.weight baseStack (index,true)).mp valid.ranked
  refine ⟨rfl,fun query => (frame query).trans (valid.frame query),readable,?_,?_,rankedPrefix,?_,coherent⟩
  · intro query queryNode member queryPresent clamp
    have smaller := before (query,true) member rfl
    have different : query ≠ index := by intro same; subst query; exact Nat.lt_irrefl _ smaller
    simpa only [effective,unchanged query different] using valid.pending query queryNode (by simp [member]) queryPresent clamp
  · intro task member
    exact valid.known task (by simp [member])
  · have previous := valid.budget
    dsimp only at previous ⊢
    rw [potential_push] at previous
    simp only [cost,↓reduceIte] at previous
    omega

end DuplicatePrefix.GeneralBorrowExposedKnownRootInvariant
