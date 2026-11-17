import duplicate_prefix.GeneralBorrowFrontier
namespace DuplicatePrefix.GeneralBorrowPresence
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowTopology DuplicatePrefix.GeneralBorrowFrontier
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
abbrev nodeData (tree : TraversalTree) (index : Nat) := tree.nodes[index]?.getD ⟨none,[]⟩

def ParentClosed (tree : TraversalTree) (present : Nat → Prop) : Prop :=
  ∀ current, present current → ∀ parent, (nodeData tree current).parent = some parent → present parent

def ChildClosed (tree : TraversalTree) (present : Nat → Prop) : Prop :=
  ∀ current, present current → ∀ child ∈ (nodeData tree current).children, present child

theorem ancestor_zero (tree : TraversalTree) (current : Nat) :
    sourceAncestorPath tree 0 current = [current] := rfl

theorem ancestor_succ (tree : TraversalTree) (fuel current : Nat) :
    sourceAncestorPath tree (fuel+1) current = match (nodeData tree current).parent with
      | none => [current]
      | some parent => current :: sourceAncestorPath tree fuel parent := rfl

theorem ancestors_present (tree : TraversalTree) (present : Nat → Prop)
    (closed : ParentClosed tree present) (fuel current : Nat) (initial : present current) :
    ∀ node ∈ sourceAncestorPath tree fuel current, present node := by
  induction fuel generalizing current with
  | zero =>
    intro node member
    have same : node = current := by simpa only [ancestor_zero,List.mem_singleton] using member
    simpa only [same] using initial
  | succ fuel ih =>
    intro node member
    rw [ancestor_succ] at member
    cases parentEq : (nodeData tree current).parent with
    | none =>
      simp only [parentEq,List.mem_singleton] at member
      simpa only [member] using initial
    | some parent =>
      simp only [parentEq,List.mem_cons] at member
      rcases member with same | above
      · simpa only [same] using initial
      · exact ih parent (closed current initial parent parentEq) node above

theorem foreign_present (tree : TraversalTree) (present : Nat → Prop)
    (closed : ChildClosed tree present) (skips : List Nat) (fuel root : Nat) (initial : present root) :
    ∀ event ∈ sourceForeignPostorder tree skips fuel root, present event.node := by
  induction fuel generalizing root with
  | zero => simp [foreign_zero]
  | succ fuel ih =>
    intro event member
    rw [foreign_succ] at member
    split at member
    · simp at member
    · rcases List.mem_append.mp member with nested | here
      · obtain ⟨child,childMember,inChild⟩ := List.mem_flatMap.mp nested
        exact ih child (closed root initial child (List.mem_reverse.mp childMember)) event inChild
      · have same : event = ⟨root,.ForeignAccess⟩ := by simpa using here
        simpa only [same] using initial

theorem roots_present (tree : TraversalTree) (present : Nat → Prop)
    (closed : ChildClosed tree present) (path : List Nat)
    (initial : ∀ node ∈ path, present node) (mode : ChildrenVisitMode) (previous : Option Nat) (isStart : Bool) :
    ∀ root ∈ sourceForeignRootsGo tree mode path previous isStart, present root := by
  induction path generalizing previous isStart with
  | nil => simp [roots_nil]
  | cons current rest ih =>
    intro root member
    rw [roots_cons] at member
    rcases List.mem_append.mp member with here | there
    · unfold deferredHeads at here
      split at here
      · have childMember := (List.mem_filter.mp here).1
        exact closed current (initial current (by simp)) root (List.mem_reverse.mp childMember)
      · simp at here
    · exact ih (fun node member => initial node (by simp [member])) (some current) false root there

theorem traversal_present (tree : TraversalTree) (present : Nat → Prop)
    (parentClosed : ParentClosed tree present) (childClosed : ChildClosed tree present)
    (anchor : Nat) (initial : present anchor) (mode : ChildrenVisitMode) (skips : List Nat) :
    ∀ event ∈ (tree.traverse anchor mode skips).2, present event.node := by
  intro event member
  have ancestors := ancestors_present tree present parentClosed tree.nodes.size anchor initial
  have roots := roots_present tree present childClosed (tree.ancestorPath anchor) ancestors mode none true
  simp only [TraversalTree.traverse] at member
  rcases List.mem_append.mp member with localEvent | foreignEvent
  · obtain ⟨node,inPath,same⟩ := List.mem_map.mp localEvent
    subst event
    exact ancestors node inPath
  · obtain ⟨root,inRoots,inRoot⟩ := List.mem_flatMap.mp foreignEvent
    exact foreign_present tree present childClosed skips tree.nodes.size root (roots root inRoots) event inRoot
end DuplicatePrefix.GeneralBorrowPresence

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowPresence." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved generic visitor presence dependency {dependency}"
