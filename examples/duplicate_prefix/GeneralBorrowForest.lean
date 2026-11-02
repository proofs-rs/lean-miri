import duplicate_prefix.GeneralBorrowTopology
namespace DuplicatePrefix.GeneralBorrowForest
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowTopology
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
/-- A ranked reciprocal finite forest. These are only graph-data invariants. -/
structure Forest (tree : TraversalTree) where
  rank : Nat → Nat
  parents : ParentRanks tree rank
  childrenDistinct : ∀ index (valid : index < tree.nodes.size), tree.nodes[index].children.Nodup
  childParent : ∀ parent (valid : parent < tree.nodes.size) child,
    child ∈ tree.nodes[parent].children →
      ∃ childValid : child < tree.nodes.size, tree.nodes[child].parent = some parent
  parentChild : ∀ child (valid : child < tree.nodes.size) parent,
    tree.nodes[child].parent = some parent →
      ∃ parentValid : parent < tree.nodes.size, child ∈ tree.nodes[parent].children

inductive Desc (tree : TraversalTree) : Nat → Nat → Prop
  | refl (index : Nat) (valid : index < tree.nodes.size) : Desc tree index index
  | step {root parent child : Nat} (earlier : Desc tree root parent)
      (valid : child < tree.nodes.size) (edge : tree.nodes[child].parent = some parent) :
      Desc tree root child

theorem Desc.valid {tree : TraversalTree} {root node : Nat} (path : Desc tree root node) :
    root < tree.nodes.size ∧ node < tree.nodes.size := by
  induction path with
  | refl valid => exact ⟨valid,valid⟩
  | step earlier valid edge ih => exact ⟨ih.1,valid⟩

theorem Desc.rank_le {tree : TraversalTree} (forest : Forest tree)
    {root node : Nat} (path : Desc tree root node) : forest.rank root ≤ forest.rank node := by
  induction path with
  | refl => exact Nat.le_refl _
  | step earlier valid edge ih =>
    exact Nat.le_trans ih (Nat.le_of_lt (forest.parents _ valid _ edge).2)

theorem Desc.comparable {tree : TraversalTree} {left right node : Nat}
    (first : Desc tree left node) (second : Desc tree right node) :
    Desc tree left right ∨ Desc tree right left := by
  induction first generalizing right with
  | refl valid => exact .inr second
  | step earlier valid edge ih =>
    cases second with
    | refl => exact .inl (.step earlier valid edge)
    | step previous otherValid otherEdge =>
      have same := Option.some.inj (edge.symm.trans otherEdge)
      cases same
      exact ih previous

theorem Desc.parent {tree : TraversalTree} {root child parent : Nat}
    (path : Desc tree root child) (valid : child < tree.nodes.size)
    (edge : tree.nodes[child].parent = some parent) :
    root = child ∨ Desc tree root parent := by
  cases path with
  | refl => exact .inl rfl
  | step earlier otherValid otherEdge =>
    have same := Option.some.inj (otherEdge.symm.trans edge)
    cases same
    exact .inr earlier

theorem siblings_disjoint {tree : TraversalTree} (forest : Forest tree)
    (parent left right node : Nat) (parentValid : parent < tree.nodes.size)
    (leftMember : left ∈ tree.nodes[parent].children)
    (rightMember : right ∈ tree.nodes[parent].children) (different : left ≠ right) :
    ¬ (Desc tree left node ∧ Desc tree right node) := by
  obtain ⟨leftValid,leftEdge⟩ := forest.childParent parent parentValid left leftMember
  obtain ⟨rightValid,rightEdge⟩ := forest.childParent parent parentValid right rightMember
  intro ⟨fromLeft,fromRight⟩
  rcases fromLeft.comparable fromRight with leftToRight | rightToLeft
  · rcases leftToRight.parent rightValid rightEdge with same | ancestor
    · exact different same
    · have lower := ancestor.rank_le forest
      have higher := (forest.parents left leftValid parent leftEdge).2
      omega
  · rcases rightToLeft.parent leftValid leftEdge with same | ancestor
    · exact different same.symm
    · have lower := ancestor.rank_le forest
      have higher := (forest.parents right rightValid parent rightEdge).2
      omega
theorem Desc.trans {tree : TraversalTree} {root middle node : Nat}
    (first : Desc tree root middle) (second : Desc tree middle node) : Desc tree root node := by
  induction second with
  | refl => exact first
  | step earlier valid edge ih => exact .step ih valid edge

theorem foreign_desc (tree : TraversalTree) (forest : Forest tree) (skips : List Nat)
    (fuel root : Nat) (valid : root < tree.nodes.size) (event : TraversalEvent)
    (member : event ∈ sourceForeignPostorder tree skips fuel root) : Desc tree root event.node := by
  induction fuel generalizing root with
  | zero => simp [foreign_zero] at member
  | succ fuel ih =>
    rw [foreign_succ] at member
    split at member
    · simp at member
    · simp only [Array.getElem?_eq_getElem valid,Option.getD_some] at member
      rcases List.mem_append.mp member with nested | here
      · obtain ⟨child,childMember,inChild⟩ := List.mem_flatMap.mp nested
        have childData := forest.childParent root valid child (List.mem_reverse.mp childMember)
        exact (Desc.step (.refl root valid) childData.1 childData.2).trans (ih child childData.1 inChild)
      · have same : event = ⟨root,.ForeignAccess⟩ := by simpa using here
        subst event
        exact .refl root valid

theorem foreign_nodes_nodup (tree : TraversalTree) (forest : Forest tree) (skips : List Nat)
    (fuel root : Nat) (valid : root < tree.nodes.size) :
    ((sourceForeignPostorder tree skips fuel root).map TraversalEvent.node).Nodup := by
  induction fuel generalizing root with
  | zero => simp [foreign_zero]
  | succ fuel ih =>
    rw [foreign_succ]
    split
    · simp
    · simp only [Array.getElem?_eq_getElem valid,Option.getD_some,List.map_append,List.map_flatMap,
        List.map_cons,List.map_nil]
      have childrenDistinct : tree.nodes[root].children.reverse.Nodup :=
        List.pairwise_reverse.mpr ((forest.childrenDistinct root valid).imp (fun different => Ne.symm different))
      apply List.nodup_append.mpr
      refine ⟨?_,by simp,?_⟩
      · apply List.pairwise_flatMap.mpr
        constructor
        · intro child childMember
          exact ih child (forest.childParent root valid child (List.mem_reverse.mp childMember)).1
        · apply childrenDistinct.imp_of_mem
          intro left right leftMember rightMember different nodeLeft inLeft nodeRight inRight same
          obtain ⟨leftEvent,leftIn,leftNode⟩ := List.mem_map.mp inLeft
          obtain ⟨rightEvent,rightIn,rightNode⟩ := List.mem_map.mp inRight
          have leftMember' := List.mem_reverse.mp leftMember
          have rightMember' := List.mem_reverse.mp rightMember
          have leftValid := (forest.childParent root valid left leftMember').1
          have rightValid := (forest.childParent root valid right rightMember').1
          have fromLeft := foreign_desc tree forest skips fuel left leftValid leftEvent leftIn
          have fromRight := foreign_desc tree forest skips fuel right rightValid rightEvent rightIn
          have sameNodes : leftEvent.node = rightEvent.node := leftNode.trans (same.trans rightNode.symm)
          apply siblings_disjoint forest root left right leftEvent.node valid leftMember' rightMember' different
          exact ⟨fromLeft,by rw [sameNodes]; exact fromRight⟩
      · intro node inChildren last inLast same
        have lastEq : last = root := by simpa using inLast
        obtain ⟨child,childMember,inChild⟩ := List.mem_flatMap.mp inChildren
        obtain ⟨event,eventIn,eventNode⟩ := List.mem_map.mp inChild
        have childData := forest.childParent root valid child (List.mem_reverse.mp childMember)
        have lower := (foreign_desc tree forest skips fuel child childData.1 event eventIn).rank_le forest
        have higher := (forest.parents child childData.1 root childData.2).2
        have sameNode : event.node = root := eventNode.trans (same.trans lastEq)
        rw [sameNode] at lower
        omega

end DuplicatePrefix.GeneralBorrowForest

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowForest." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general forest dependency {dependency}"
