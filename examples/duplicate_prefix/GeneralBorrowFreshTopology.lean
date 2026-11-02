import duplicate_prefix.GeneralBorrowTerminal
namespace DuplicatePrefix.GeneralBorrowFreshTopology
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowTopology DuplicatePrefix.GeneralBorrowPresence
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

set_option autoImplicit false in
/-- Data relations for appending a concrete child: old parent links are fixed,
only its parent's child list grows, and the fresh node is a childless leaf. -/
structure Extension (before after : TraversalTree) (parent : Nat) : Prop where
  parentValid : parent < before.nodes.size
  length : after.nodes.size = before.nodes.size+1
  parents : ∀ position (valid : position < before.nodes.size),
    (after.nodes[position]'(by rw [length];omega)).parent = before.nodes[position].parent
  children : ∀ position (valid : position < before.nodes.size),
    (after.nodes[position]'(by rw [length];omega)).children =
      before.nodes[position].children ++ if position = parent then [before.nodes.size] else []
  leaf : after.nodes[before.nodes.size]'(by rw [length];omega) = ⟨some parent,[]⟩

def attached (before : TraversalTree) (parent : Nat) (valid : parent < before.nodes.size) : TraversalTree :=
  ⟨(before.nodes.push ⟨some parent,[]⟩).set parent
    {before.nodes[parent] with children := before.nodes[parent].children ++ [before.nodes.size]}
    (by simp only [Array.size_push];omega)⟩

theorem attached_extension (before : TraversalTree) (parent : Nat) (valid : parent < before.nodes.size) :
    Extension before (attached before parent valid) parent := by
  refine ⟨valid,by simp only [attached,Array.size_set,Array.size_push],?_,?_,?_⟩
  · intro position bound
    simp only [attached,Array.getElem_set]
    by_cases same : parent = position
    · subst position
      simp only [ite_true]
    · simp only [same,ite_false,Array.getElem_push_lt bound]
  · intro position bound
    simp only [attached,Array.getElem_set]
    by_cases same : parent = position
    · subst position
      simp only [ite_true]
    · simp only [same,Ne.symm same,ite_false,Array.getElem_push_lt bound,List.append_nil]
  · have different : parent ≠ before.nodes.size := by omega
    simp only [attached,Array.getElem_set,different,ite_false,Array.getElem_push_eq]

theorem valid_old (before after : TraversalTree) (parent : Nat) (extension : Extension before after parent)
    (position : Nat) (valid : position < before.nodes.size) : position < after.nodes.size := by rw [extension.length];omega

def extendedRank (before : TraversalTree) (rank : Nat → Nat) (parent : Nat) : Nat → Nat :=
  fun position => if position = before.nodes.size then rank parent+1 else rank position

/-- The reciprocal, acyclic forest invariant survives actual fresh-leaf shape
extension. The new rank is constructed from the original parent's rank. -/
def extended_forest (before after : TraversalTree) (parent : Nat) (extension : Extension before after parent)
    (forest : GeneralBorrowForest.Forest before) : GeneralBorrowForest.Forest after where
  rank := extendedRank before forest.rank parent
  parents := by
    intro position valid earlier edge
    by_cases fresh : position = before.nodes.size
    · subst position
      have parentEq := congrArg TraversalNode.parent extension.leaf
      have same : earlier = parent := Option.some.inj (edge.symm.trans parentEq)
      subst earlier
      refine ⟨valid_old before after parent extension parent extension.parentValid,?_⟩
      have notFresh : parent ≠ before.nodes.size := by have := extension.parentValid;omega
      simp [extendedRank,notFresh]
    · have old : position < before.nodes.size := by rw [extension.length] at valid;omega
      have original : before.nodes[position].parent = some earlier := (extension.parents position old).symm.trans edge
      obtain ⟨bound,smaller⟩ := forest.parents position old earlier original
      refine ⟨valid_old before after parent extension earlier bound,?_⟩
      have notFresh : earlier ≠ before.nodes.size := by omega
      simpa only [extendedRank,fresh,notFresh,ite_false] using smaller
  childrenDistinct := by
    intro position valid
    by_cases fresh : position = before.nodes.size
    · subst position
      rw [extension.leaf]
      simp
    · have old : position < before.nodes.size := by rw [extension.length] at valid;omega
      rw [extension.children position old]
      by_cases same : position = parent
      · rw [if_pos same]
        apply List.nodup_append.mpr
        refine ⟨forest.childrenDistinct position old,by simp,?_⟩
        intro child member other singleton equal
        have otherEq : other = before.nodes.size := by simpa only [List.mem_singleton] using singleton
        have bounded := (forest.childParent position old child member).choose
        omega
      · simp only [same,ite_false,List.append_nil]
        exact forest.childrenDistinct position old
  childParent := by
    intro position valid child member
    by_cases fresh : position = before.nodes.size
    · subst position
      rw [extension.leaf] at member
      simp at member
    · have old : position < before.nodes.size := by rw [extension.length] at valid;omega
      rw [extension.children position old] at member
      rcases List.mem_append.mp member with original | appended
      · obtain ⟨bound,edge⟩ := forest.childParent position old child original
        exact ⟨valid_old before after parent extension child bound,(extension.parents child bound).trans edge⟩
      · by_cases same : position = parent
        · subst position
          simp only [ite_true,List.mem_singleton] at appended
          subst child
          exact ⟨by rw [extension.length];omega,congrArg TraversalNode.parent extension.leaf⟩
        · simp only [same,ite_false,List.not_mem_nil] at appended
  parentChild := by
    intro position valid earlier edge
    by_cases fresh : position = before.nodes.size
    · subst position
      have parentEq := congrArg TraversalNode.parent extension.leaf
      have same : earlier = parent := Option.some.inj (edge.symm.trans parentEq)
      subst earlier
      refine ⟨valid_old before after parent extension parent extension.parentValid,?_⟩
      rw [extension.children parent extension.parentValid]
      simp
    · have old : position < before.nodes.size := by rw [extension.length] at valid;omega
      have original : before.nodes[position].parent = some earlier := (extension.parents position old).symm.trans edge
      obtain ⟨bound,member⟩ := forest.parentChild position old earlier original
      refine ⟨valid_old before after parent extension earlier bound,?_⟩
      rw [extension.children earlier bound]
      exact List.mem_append_left _ member

/-- Appending a leaf does not change an old node's ancestor path at any fuel.
Only the old forest's parent-bounds condition is needed. -/
theorem ancestors_old (before after : TraversalTree) (parent : Nat) (extension : Extension before after parent)
    (forest : GeneralBorrowForest.Forest before) (fuel position : Nat) (valid : position < before.nodes.size) :
    sourceAncestorPath after fuel position = sourceAncestorPath before fuel position := by
  induction fuel generalizing position with
  | zero => rfl
  | succ fuel ih =>
    rw [ancestor_succ,ancestor_succ]
    have sameParent : (nodeData after position).parent = (nodeData before position).parent := by
      simp only [nodeData,Array.getElem?_eq_getElem valid,
        Array.getElem?_eq_getElem (valid_old before after parent extension position valid),Option.getD_some]
      exact extension.parents position valid
    rw [sameParent]
    cases edge : (nodeData before position).parent with
    | none => rfl
    | some earlier =>
      have bounded : earlier < before.nodes.size := by
        apply (forest.parents position valid earlier _).1
        simpa only [nodeData,Array.getElem?_eq_getElem valid,Option.getD_some] using edge
      simp only
      rw [ih earlier bounded]

/-- The fresh child's actual ancestor path is itself followed by precisely
its original parent's path, including the production path's fuel change. -/
theorem ancestors_new (before after : TraversalTree) (parent : Nat) (extension : Extension before after parent)
    (forest : GeneralBorrowForest.Forest before) :
    after.ancestorPath before.nodes.size = before.nodes.size :: before.ancestorPath parent := by
  unfold TraversalTree.ancestorPath
  rw [extension.length,ancestor_succ]
  have freshValid : before.nodes.size < after.nodes.size := by rw [extension.length];omega
  have edge : (nodeData after before.nodes.size).parent = some parent := by
    simp only [nodeData,Array.getElem?_eq_getElem freshValid,Option.getD_some,extension.leaf]
  rw [edge]
  simp only
  rw [ancestors_old before after parent extension forest before.nodes.size parent extension.parentValid]

end DuplicatePrefix.GeneralBorrowFreshTopology
#print axioms DuplicatePrefix.GeneralBorrowFreshTopology.ancestors_new
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshTopology." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved child ancestor dependency {dependency}"
