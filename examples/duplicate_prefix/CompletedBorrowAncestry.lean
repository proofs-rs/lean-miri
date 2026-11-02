import duplicate_prefix.CandidateStableCallOwnership
import duplicate_prefix.GeneralBorrowWildcardParentTagOrder

/-! Static graph consequences of the explicitly unadopted finite completion
model. These lemmas assert neither ordinary-input coverage nor adequacy of a
raw/precise permission abstraction. -/
namespace DuplicatePrefix.CompletedBorrowAncestry
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedNonleafPrimaryPath CandidateStableCallOwnership
open GeneralBorrowWildcardParentTagOrder
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem below_trans {completion : Completion} {first middle last : UniIndex}
    (left : Below completion first middle) (right : Below completion middle last) :
    Below completion first last := by
  induction right with
  | refl => exact left
  | step edge _ ih => exact .step edge ih

theorem physical_below {tree : BorrowTree} {completion : Completion}
    (complete : Completes tree completion) {first last : UniIndex}
    (physical : Path tree first last) : Below completion first last := by
  rcases complete with ⟨_,_,_,_,nodes,_,_⟩
  induction physical with
  | refl => exact .refl _
  | step _ node present edge ih => exact .step ((nodes _ node present).2.2.1 _ edge) ih

/-- A completed ancestor of a physical descendant is either above the
physical root or on that root's physical descendant chain. -/
theorem physical_suffix {tree : BorrowTree} {completion : Completion}
    (complete : Completes tree completion) {root last query : UniIndex}
    (physical : Path tree root last) (completed : Below completion query last) :
    Below completion query root ∨ Path tree root query := by
  rcases complete with ⟨_,_,_,_,nodes,_,_⟩
  induction physical generalizing query with
  | refl => exact .inl completed
  | @step parent child earlier node present edge ih =>
    cases completed with
    | refl => exact .inr (.step earlier node present edge)
    | @step otherParent _ completed prior =>
      have preserved := (nodes child node present).2.2.1 parent edge
      have same : otherParent = parent := Option.some.inj (Option.some.inj (completed.symm.trans preserved))
      subst otherParent
      exact ih prior

/-- Distinct parentless physical roots cannot share a physical descendant. -/
theorem physical_roots_unique {tree : BorrowTree} {first second last : UniIndex}
    {firstNode secondNode : TreeNode}
    (firstPresent : tree.nodes.get first = some firstNode) (firstRoot : firstNode.parent = none)
    (secondPresent : tree.nodes.get second = some secondNode) (secondRoot : secondNode.parent = none)
    (left : Path tree first last) (right : Path tree second last) : first = second := by
  induction left generalizing second secondNode with
  | refl node present =>
    cases right with
    | refl => rfl
    | step earlier other otherPresent edge =>
      have same : firstNode = other := Option.some.inj (firstPresent.symm.trans otherPresent)
      rw [←same,firstRoot] at edge
      contradiction
  | @step parent child earlier node present edge ih =>
    cases right with
    | refl =>
      have same : secondNode = node := Option.some.inj (secondPresent.symm.trans present)
      rw [←same,secondRoot] at edge
      contradiction
    | @step otherParent _ otherEarlier other otherPresent otherEdge =>
      have sameNode : node = other := Option.some.inj (present.symm.trans otherPresent)
      have sameParent : parent = otherParent := Option.some.inj (edge.symm.trans (sameNode ▸ otherEdge))
      subst otherParent
      exact ih secondPresent secondRoot otherEarlier

/-- An ancestor in another actual physical component lies above the selected
physical root in the completed ancestry. -/
theorem below_selected_root {tree : BorrowTree} {completion : Completion}
    (complete : Completes tree completion)
    {callbackRoot selectedRoot query source : UniIndex} {callbackNode selectedNode : TreeNode}
    (callbackPresent : tree.nodes.get callbackRoot = some callbackNode)
    (callbackParentless : callbackNode.parent = none)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (selectedParentless : selectedNode.parent = none)
    (different : callbackRoot ≠ selectedRoot)
    (callbackPath : Path tree callbackRoot query) (selectedPath : Path tree selectedRoot source)
    (completed : Below completion query source) : Below completion query selectedRoot := by
  rcases physical_suffix complete selectedPath completed with above | sameComponent
  · exact above
  · exact False.elim (different (physical_roots_unique callbackPresent callbackParentless
      selectedPresent selectedParentless callbackPath sameComponent))

/-- A completed edge out of a physical root is exactly an exposed older
attachment; the first physical root has no such edge. -/
theorem virtual_parent {tree : BorrowTree} {completion : Completion}
    (complete : Completes tree completion) {child parent : UniIndex} {childNode : TreeNode}
    (present : tree.nodes.get child = some childNode) (parentless : childNode.parent = none)
    (edge : completion.parents[child.toNat]? = some (some parent)) :
    ∃ parentNode, tree.nodes.get parent = some parentNode ∧ parentNode.isExposed = true ∧
      parentNode.tag.value < childNode.tag.value := by
  rcases complete with ⟨_,_,_,_,nodes,virtual,_⟩
  have member : child ∈ tree.roots := by simpa using (nodes child childNode present).2.2.2.mp parentless
  obtain ⟨position,slot⟩ := Array.getElem?_of_mem member
  have attachment := virtual position child slot
  by_cases first : position = 0
  · simp only [first,ite_true] at attachment
    rw [edge] at attachment
    cases Option.some.inj attachment
  · simp only [first,ite_false] at attachment
    obtain ⟨earlier,originRoot,origin,rootNode,originNode,_,_,rootPresent,originPresent,
      exposed,older,_,chosen⟩ := attachment
    have sameParent : parent = origin := Option.some.inj (Option.some.inj (edge.symm.trans chosen))
    have sameNode : childNode = rootNode := Option.some.inj (present.symm.trans rootPresent)
    subst parent
    subst childNode
    exact ⟨originNode,originPresent,exposed,older⟩

theorem completed_tag_le {tree : BorrowTree} {completion : Completion}
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    {first last : UniIndex} {firstNode lastNode : TreeNode}
    (firstPresent : tree.nodes.get first = some firstNode)
    (lastPresent : tree.nodes.get last = some lastNode) (completed : Below completion first last) :
    firstNode.tag.value ≤ lastNode.tag.value := by
  have edges := complete.2.2.2.2.2.2
  have nodes := complete.2.2.2.2.1
  induction completed generalizing lastNode with
  | refl =>
    have same := Option.some.inj (firstPresent.symm.trans lastPresent)
    subst lastNode
    exact Nat.le_refl _
  | @step parent child edge prior ih =>
    obtain ⟨_,⟨parentNode,parentPresent⟩,_⟩ := edges child parent edge
    have earlier := ih parentPresent
    have later : parentNode.tag.value ≤ lastNode.tag.value := by
      cases physical : lastNode.parent with
      | none =>
        obtain ⟨originNode,originPresent,_,older⟩ := virtual_parent complete lastPresent physical edge
        have same := Option.some.inj (parentPresent.symm.trans originPresent)
        subst originNode
        exact Nat.le_of_lt older
      | some actual =>
        have preserved := (nodes child lastNode lastPresent).2.2.1 actual physical
        have same : parent = actual := Option.some.inj (Option.some.inj (edge.symm.trans preserved))
        subst actual
        exact order child lastNode lastPresent parent parentNode physical parentPresent
    exact Nat.le_trans earlier later

/-- Extract the first virtual edge on a completed chain, retaining the
physical prefix below its starting query. -/
theorem physical_or_attachment {tree : BorrowTree} {completion : Completion}
    (complete : Completes tree completion) {first last : UniIndex} {firstNode : TreeNode}
    (firstPresent : tree.nodes.get first = some firstNode) (completed : Below completion first last) :
    Path tree first last ∨ ∃ origin next originNode nextNode,
      Path tree first origin ∧ tree.nodes.get origin = some originNode ∧
      originNode.isExposed = true ∧ tree.nodes.get next = some nextNode ∧
      nextNode.parent = none ∧ completion.parents[next.toNat]? = some (some origin) ∧
      Below completion next last := by
  have edges := complete.2.2.2.2.2.2
  have nodes := complete.2.2.2.2.1
  induction completed with
  | refl => exact .inl (.refl _ firstNode firstPresent)
  | @step parent child edge prior ih =>
    obtain ⟨⟨childNode,childPresent⟩,_,_⟩ := edges child parent edge
    rcases ih with physicalPath | ⟨origin,next,originNode,nextNode,path,present,exposed,nextPresent,parentless,chosen,after⟩
    · cases physical : childNode.parent with
      | none =>
        obtain ⟨parentNode,parentPresent,exposed,_⟩ := virtual_parent complete childPresent physical edge
        exact .inr ⟨parent,child,parentNode,childNode,physicalPath,parentPresent,exposed,
          childPresent,physical,edge,.refl child⟩
      | some actual =>
        have preserved := (nodes child childNode childPresent).2.2.1 actual physical
        have same : parent = actual := Option.some.inj (Option.some.inj (edge.symm.trans preserved))
        subst actual
        exact .inl (.step physicalPath childNode childPresent physical)
    · exact .inr ⟨origin,next,originNode,nextNode,path,present,exposed,nextPresent,parentless,
        chosen,.step edge after⟩

theorem path_trans {tree : BorrowTree} {first middle last : UniIndex}
    (left : Path tree first middle) (right : Path tree middle last) : Path tree first last := by
  induction right with
  | refl => exact left
  | step _ node present edge ih => exact .step ih node present edge

/-- Cross-component completed ancestry has a real exposed attachment below
the callback query, older than the actual selected normal root. -/
theorem cross_root_origin {tree : BorrowTree} {completion : Completion}
    (complete : Completes tree completion) (order : ParentTagOrder tree)
    {callbackRoot selectedRoot query source : UniIndex} {callbackNode selectedNode queryNode : TreeNode}
    (callbackPresent : tree.nodes.get callbackRoot = some callbackNode)
    (callbackParentless : callbackNode.parent = none)
    (selectedPresent : tree.nodes.get selectedRoot = some selectedNode)
    (selectedParentless : selectedNode.parent = none)
    (queryPresent : tree.nodes.get query = some queryNode)
    (different : callbackRoot ≠ selectedRoot)
    (callbackPath : Path tree callbackRoot query) (selectedPath : Path tree selectedRoot source)
    (completed : Below completion query source) :
    ∃ origin originNode, tree.nodes.get origin = some originNode ∧ originNode.isExposed = true ∧
      Path tree query origin ∧ Below completion origin selectedRoot ∧
      Below completion origin source ∧ originNode.tag.value ≤ selectedNode.tag.value := by
  have short := below_selected_root complete callbackPresent callbackParentless selectedPresent
    selectedParentless different callbackPath selectedPath completed
  rcases physical_or_attachment complete queryPresent short with physical | attachment
  · have same := physical_roots_unique callbackPresent callbackParentless selectedPresent
      selectedParentless (path_trans callbackPath physical) (.refl _ selectedNode selectedPresent)
    exact False.elim (different same)
  · obtain ⟨origin,next,originNode,nextNode,path,present,exposed,_,_,edge,after⟩ := attachment
    have originSelected : Below completion origin selectedRoot :=
      below_trans (.step edge (.refl origin)) after
    exact ⟨origin,originNode,present,exposed,path,originSelected,
      below_trans originSelected (physical_below complete selectedPath),
      completed_tag_le complete order present selectedPresent originSelected⟩

/-- Earlier-component attachments connect the first physical root to every
actual root, without a sorted-root-tag premise or an internal source grant
in the first component. -/
theorem root_zero_below {tree : BorrowTree} {completion : Completion}
    (complete : Completes tree completion) {zero selectedRoot source : UniIndex} {position : Nat}
    (zeroSlot : tree.roots[0]? = some zero) (selectedSlot : tree.roots[position]? = some selectedRoot)
    (selectedPath : Path tree selectedRoot source) : Below completion zero source := by
  have virtual := complete.2.2.2.2.2.1
  have allRoots : ∀ (position : Nat) (root : UniIndex), tree.roots[position]? = some root → Below completion zero root := by
    intro position
    induction position using Nat.strongRecOn with
    | ind position ih =>
      intro root slot
      by_cases first : position = 0
      · have same : zero = root := Option.some.inj (zeroSlot.symm.trans (by simpa only [first] using slot))
        subst root
        exact .refl zero
      · have attachment := virtual position root slot
        simp only [first,ite_false] at attachment
        obtain ⟨earlier,originRoot,origin,_,_,smaller,earlierSlot,_,_,_,_,path,edge⟩ := attachment
        exact .step edge (below_trans (ih earlier smaller originRoot earlierSlot) (physical_below complete path))
  exact below_trans (allRoots position selectedRoot selectedSlot) (physical_below complete selectedPath)

end DuplicatePrefix.CompletedBorrowAncestry

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CompletedBorrowAncestry." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved completed ancestry dependency {dependency}"
