import duplicate_prefix.GeneralBorrowFreshTopology
namespace DuplicatePrefix.GeneralBorrowFreshReuseTopology
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowTopology DuplicatePrefix.GeneralBorrowPresence
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

set_option autoImplicit false in
/-- A vacant topology slot is an isolated dummy root. Reuse keeps the table
length, replaces that slot by a leaf and attaches it to an existing parent. -/
structure Extension (before after : TraversalTree) (index parent : Nat) : Prop where
  valid : index < before.nodes.size
  parentValid : parent < before.nodes.size
  different : parent ≠ index
  vacant : before.nodes[index] = ⟨none,[]⟩
  length : after.nodes.size = before.nodes.size
  parents : ∀ position (valid : position < before.nodes.size), position ≠ index →
    (after.nodes[position]'(by rw [length];exact valid)).parent = before.nodes[position].parent
  children : ∀ position (valid : position < before.nodes.size), position ≠ index →
    (after.nodes[position]'(by rw [length];exact valid)).children =
      before.nodes[position].children ++ if position = parent then [index] else []
  leaf : after.nodes[index]'(by rw [length];exact valid) = ⟨some parent,[]⟩

def attached (before : TraversalTree) (index parent : Nat)
    (valid : index < before.nodes.size) (parentValid : parent < before.nodes.size) : TraversalTree :=
  ⟨(before.nodes.set index ⟨some parent,[]⟩ valid).set parent
    {before.nodes[parent] with children := before.nodes[parent].children ++ [index]}
    (by simpa only [Array.size_set] using parentValid)⟩

theorem attached_extension (before : TraversalTree) (index parent : Nat)
    (valid : index < before.nodes.size) (parentValid : parent < before.nodes.size)
    (different : parent ≠ index) (vacant : before.nodes[index] = ⟨none,[]⟩) :
    Extension before (attached before index parent valid parentValid) index parent := by
  refine ⟨valid,parentValid,different,vacant,by simp only [attached,Array.size_set],?_,?_,?_⟩
  · intro position bound old
    simp only [attached,Array.getElem_set]
    by_cases same : parent = position
    · subst position;simp only [ite_true]
    · simp only [same,ite_false,Ne.symm old]
  · intro position bound old
    simp only [attached,Array.getElem_set]
    by_cases same : parent = position
    · subst position;simp only [ite_true]
    · simp only [same,Ne.symm same,ite_false,Ne.symm old,List.append_nil]
  · simp only [attached,Array.getElem_set,different,ite_false,ite_true]

theorem no_parent (before : TraversalTree) (forest : GeneralBorrowForest.Forest before)
    (index : Nat) (valid : index < before.nodes.size) (vacant : before.nodes[index] = ⟨none,[]⟩)
    (position : Nat) (bound : position < before.nodes.size) : before.nodes[position].parent ≠ some index := by
  intro edge
  obtain ⟨_,member⟩ := forest.parentChild position bound index edge
  rw [vacant] at member
  cases member

theorem no_child (before : TraversalTree) (forest : GeneralBorrowForest.Forest before)
    (index : Nat) (valid : index < before.nodes.size) (vacant : before.nodes[index] = ⟨none,[]⟩)
    (position : Nat) (bound : position < before.nodes.size) : index ∉ before.nodes[position].children := by
  intro member
  obtain ⟨_,edge⟩ := forest.childParent position bound index member
  rw [vacant] at edge
  cases edge

def extendedRank (rank : Nat → Nat) (index parent : Nat) : Nat → Nat :=
  fun position => if position = index then rank parent+1 else rank position

/-- Replacing an isolated vacant slot by a fresh attached leaf preserves the
reciprocal acyclic forest. Old references to that slot are ruled out by the
old forest plus vacancy, rather than silently treated as fresh references. -/
def extended_forest (before after : TraversalTree) (index parent : Nat)
    (extension : Extension before after index parent) (forest : GeneralBorrowForest.Forest before) :
    GeneralBorrowForest.Forest after where
  rank := extendedRank forest.rank index parent
  parents := by
    intro position valid earlier edge
    have old : position < before.nodes.size := by rw [←extension.length];exact valid
    by_cases fresh : position = index
    · subst position
      have same : earlier = parent := Option.some.inj (edge.symm.trans (congrArg TraversalNode.parent extension.leaf))
      subst earlier
      refine ⟨by rw [extension.length];exact extension.parentValid,?_⟩
      simp [extendedRank,extension.different]
    · have original : before.nodes[position].parent = some earlier :=
        (extension.parents position old fresh).symm.trans edge
      obtain ⟨bound,smaller⟩ := forest.parents position old earlier original
      have different : earlier ≠ index := by
        intro equal
        subst earlier
        exact no_parent before forest index extension.valid extension.vacant position old original
      refine ⟨by rw [extension.length];exact bound,?_⟩
      simpa only [extendedRank,fresh,different,ite_false] using smaller
  childrenDistinct := by
    intro position valid
    have old : position < before.nodes.size := by rw [←extension.length];exact valid
    by_cases fresh : position = index
    · subst position
      rw [extension.leaf]
      simp
    · rw [extension.children position old fresh]
      by_cases same : position = parent
      · rw [if_pos same]
        apply List.nodup_append.mpr
        refine ⟨forest.childrenDistinct position old,by simp,?_⟩
        intro child member other singleton equal
        have otherEq : other = index := by simpa only [List.mem_singleton] using singleton
        subst other
        subst child
        exact no_child before forest index extension.valid extension.vacant position old member
      · simp only [same,ite_false,List.append_nil]
        exact forest.childrenDistinct position old
  childParent := by
    intro position valid child member
    have old : position < before.nodes.size := by rw [←extension.length];exact valid
    by_cases fresh : position = index
    · subst position
      rw [extension.leaf] at member
      cases member
    · rw [extension.children position old fresh] at member
      rcases List.mem_append.mp member with original | appended
      · obtain ⟨bound,edge⟩ := forest.childParent position old child original
        have different : child ≠ index := by
          intro equal
          subst child
          exact no_child before forest index extension.valid extension.vacant position old original
        refine ⟨by rw [extension.length];exact bound,?_⟩
        exact (extension.parents child bound different).trans edge
      · by_cases same : position = parent
        · subst position
          simp only [ite_true,List.mem_singleton] at appended
          subst child
          exact ⟨by rw [extension.length];exact extension.valid,congrArg TraversalNode.parent extension.leaf⟩
        · simp only [same,ite_false,List.not_mem_nil] at appended
  parentChild := by
    intro position valid earlier edge
    have old : position < before.nodes.size := by rw [←extension.length];exact valid
    by_cases fresh : position = index
    · subst position
      have same : earlier = parent := Option.some.inj (edge.symm.trans (congrArg TraversalNode.parent extension.leaf))
      subst earlier
      refine ⟨by rw [extension.length];exact extension.parentValid,?_⟩
      rw [extension.children parent extension.parentValid extension.different]
      simp
    · have original : before.nodes[position].parent = some earlier :=
        (extension.parents position old fresh).symm.trans edge
      obtain ⟨bound,member⟩ := forest.parentChild position old earlier original
      have different : earlier ≠ index := by
        intro equal
        subst earlier
        exact no_parent before forest index extension.valid extension.vacant position old original
      refine ⟨by rw [extension.length];exact bound,?_⟩
      rw [extension.children earlier bound different]
      exact List.mem_append_left _ member

/-- Reuse changes no old nonvacant ancestor path at any fixed fuel. -/
theorem ancestors_old (before after : TraversalTree) (index parent : Nat)
    (extension : Extension before after index parent) (forest : GeneralBorrowForest.Forest before)
    (fuel position : Nat) (valid : position < before.nodes.size) (different : position ≠ index) :
    sourceAncestorPath after fuel position = sourceAncestorPath before fuel position := by
  induction fuel generalizing position with
  | zero => rfl
  | succ fuel ih =>
    rw [ancestor_succ,ancestor_succ]
    have afterValid : position < after.nodes.size := by rw [extension.length];exact valid
    have sameParent : (nodeData after position).parent = (nodeData before position).parent := by
      simp only [nodeData,Array.getElem?_eq_getElem valid,Array.getElem?_eq_getElem afterValid,Option.getD_some]
      exact extension.parents position valid different
    rw [sameParent]
    cases edge : (nodeData before position).parent with
    | none => rfl
    | some earlier =>
      have original : before.nodes[position].parent = some earlier := by
        simpa only [nodeData,Array.getElem?_eq_getElem valid,Option.getD_some] using edge
      have bounded := (forest.parents position valid earlier original).1
      have earlierDifferent : earlier ≠ index := by
        intro equal
        subst earlier
        exact no_parent before forest index extension.valid extension.vacant position valid original
      simp only
      rw [ih earlier bounded earlierDifferent]
private theorem terminal_step (tree : TraversalTree) (fuel current : Nat)
    (terminal : (nodeData tree (sourceAncestorPath tree fuel current).getLast!).parent = none) :
    sourceAncestorPath tree (fuel+1) current = sourceAncestorPath tree fuel current := by
  induction fuel generalizing current with
  | zero =>
    have edge : (nodeData tree current).parent = none := by simpa [ancestor_zero] using terminal
    rw [ancestor_succ,edge,ancestor_zero]
  | succ fuel ih =>
    rw [ancestor_succ] at terminal
    rw [ancestor_succ,ancestor_succ]
    cases edge : (nodeData tree current).parent with
    | none => simp only [edge]
    | some earlier =>
      simp only [edge] at terminal ⊢
      have lastEq : (current :: sourceAncestorPath tree fuel earlier).getLast! =
          (sourceAncestorPath tree fuel earlier).getLast! := by
        simp only [List.getLast!_eq_getLast?_getD,List.getLast?_cons_of_ne_nil
          (GeneralBorrowTerminal.ancestors_nonempty tree fuel earlier)]
      rw [lastEq] at terminal
      rw [ih earlier terminal]

/-- A path avoiding one vacant slot needs at most table-size minus one fuel.
This discharges the production ancestorPath fuel difference on index reuse. -/
theorem short_full (tree : TraversalTree) (forest : GeneralBorrowForest.Forest tree)
    (index : Nat) (valid : index < tree.nodes.size) (vacant : tree.nodes[index] = ⟨none,[]⟩)
    (current : Nat) (bounded : current < tree.nodes.size) (different : current ≠ index) :
    sourceAncestorPath tree (tree.nodes.size-1) current = tree.ancestorPath current := by
  have closed : ParentClosed tree (fun position => position < tree.nodes.size ∧ position ≠ index) := by
    intro position known earlier edge
    have original : tree.nodes[position].parent = some earlier := by
      simpa only [nodeData,Array.getElem?_eq_getElem known.1,Option.getD_some] using edge
    refine ⟨(forest.parents position known.1 earlier original).1,?_⟩
    intro equal
    subst earlier
    exact no_parent tree forest index valid vacant position known.1 original
  have present := ancestors_present tree (fun position => position < tree.nodes.size ∧ position ≠ index)
    closed (tree.nodes.size-1) current ⟨bounded,different⟩
  have data := ancestors_data tree forest.rank forest.parents (tree.nodes.size-1) current bounded
  have subset : sourceAncestorPath tree (tree.nodes.size-1) current ⊆ (List.range tree.nodes.size).erase index := by
    intro position member
    exact (List.mem_erase_of_ne (present position member).2).mpr (List.mem_range.mpr (present position member).1)
  have bound := data.1.length_le_of_subset subset
  rw [List.length_erase_of_mem (List.mem_range.mpr valid),List.length_range] at bound
  have terminal : (nodeData tree (sourceAncestorPath tree (tree.nodes.size-1) current).getLast!).parent = none := by
    rcases GeneralBorrowTerminal.terminal_or_full tree forest (tree.nodes.size-1) current bounded with terminal | full
    · exact terminal
    · omega
  have stable := terminal_step tree (tree.nodes.size-1) current terminal
  have fuelEq : tree.nodes.size-1+1 = tree.nodes.size := by omega
  simpa only [fuelEq,TraversalTree.ancestorPath] using stable.symm

/-- The reused leaf's complete actual ancestor path is the new index followed
by exactly the original parent's complete path. -/
theorem ancestors_new (before after : TraversalTree) (index parent : Nat)
    (extension : Extension before after index parent) (forest : GeneralBorrowForest.Forest before) :
    after.ancestorPath index = index :: before.ancestorPath parent := by
  have validAfter : index < after.nodes.size := by rw [extension.length];exact extension.valid
  have edge : (nodeData after index).parent = some parent := by
    simp only [nodeData,Array.getElem?_eq_getElem validAfter,Option.getD_some,extension.leaf]
  have fuelEq : before.nodes.size = (before.nodes.size-1)+1 := by have := extension.valid;omega
  have first : sourceAncestorPath after before.nodes.size index =
      index :: sourceAncestorPath after (before.nodes.size-1) parent := by
    conv => lhs;rw [fuelEq,ancestor_succ]
    rw [edge]
  change sourceAncestorPath after after.nodes.size index = _
  rw [extension.length,first,ancestors_old before after index parent extension forest (before.nodes.size-1) parent
    extension.parentValid extension.different,
    short_full before forest index extension.valid extension.vacant parent extension.parentValid extension.different]

end DuplicatePrefix.GeneralBorrowFreshReuseTopology
#print axioms DuplicatePrefix.GeneralBorrowFreshReuseTopology.ancestors_old

#print axioms DuplicatePrefix.GeneralBorrowFreshReuseTopology.ancestors_new
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshReuseTopology." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved reusable topology dependency {dependency}"
