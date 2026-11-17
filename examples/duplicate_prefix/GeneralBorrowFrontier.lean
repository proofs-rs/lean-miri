import duplicate_prefix.GeneralBorrowForest
namespace DuplicatePrefix.GeneralBorrowFrontier
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowTopology DuplicatePrefix.GeneralBorrowForest
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
private def sourceHelper (suffix : String) : CoreM Name := do
  let candidates := (← getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith suffix then some name else none
  match candidates with
  | [name] => pure name
  | _ => throwError "expected actual frontier helper {suffix}; found {candidates.length}"
elab "sourceForeignRootsGo" : term => return mkConst (← sourceHelper ".TraversalTree.initialForeignRoots.go")
elab "sourceForeignRoots" : term => return mkConst (← sourceHelper ".TraversalTree.initialForeignRoots")
elab "sourceAncestorHead" : term => return mkConst (← sourceHelper ".TraversalTree.ancestorPathAux_head")

inductive Spine (tree : TraversalTree) : List Nat → Prop
  | nil : Spine tree []
  | cons {current : Nat} {rest : List Nat} (valid : current < tree.nodes.size)
      (tail : Spine tree rest)
      (edge : ∀ parent, rest.head? = some parent → tree.nodes[current].parent = some parent) :
      Spine tree (current :: rest)

theorem Spine.bounded {tree : TraversalTree} {path : List Nat} (spine : Spine tree path)
    (node : Nat) (member : node ∈ path) : node < tree.nodes.size := by
  induction spine with
  | nil => simp at member
  | cons valid tail edge ih =>
    rcases List.mem_cons.mp member with same | later
    · subst node; exact valid
    · exact ih later

theorem ancestors_spine (tree : TraversalTree) (forest : Forest tree)
    (fuel current : Nat) (valid : current < tree.nodes.size) :
    Spine tree (sourceAncestorPath tree fuel current) := by
  induction fuel generalizing current with
  | zero =>
    unfold_source_ancestors
    exact .cons valid .nil (by simp)
  | succ fuel ih =>
    unfold_source_ancestors
    simp only [Array.getElem?_eq_getElem valid,Option.getD_some]
    cases parentEq : tree.nodes[current].parent with
    | none => exact .cons valid .nil (by simp)
    | some parent =>
      have parentValid := (forest.parents current valid parent parentEq).1
      refine .cons valid (ih parent parentValid) ?_
      intro ancestor head
      have parentHead : (sourceAncestorPath tree fuel parent).head? = some parent := by
        exact sourceAncestorHead tree fuel parent
      have same := Option.some.inj (parentHead.symm.trans head)
      subst ancestor
      exact parentEq
theorem Spine.desc_head {tree : TraversalTree} (current : Nat) (rest : List Nat)
    (spine : Spine tree (current::rest)) (node : Nat) (member : node ∈ current::rest) :
    Desc tree node current := by
  induction rest generalizing current with
  | nil =>
    have same : node = current := by simpa using member
    subst node
    exact .refl current (spine.bounded current (by simp))
  | cons parent tail ih =>
    cases spine with
    | cons valid tailSpine edge =>
      rcases List.mem_cons.mp member with same | later
      · subst node; exact .refl current valid
      · exact .step (ih parent tailSpine later) valid (edge parent rfl)

def DisjointSubtrees (tree : TraversalTree) (left right : Nat) : Prop :=
  ∀ node, ¬ (Desc tree left node ∧ Desc tree right node)

theorem disjoint_symm {tree : TraversalTree} {left right : Nat}
    (separate : DisjointSubtrees tree left right) : DisjointSubtrees tree right left := by
  intro node ⟨rightPath,leftPath⟩
  exact separate node ⟨leftPath,rightPath⟩

theorem disjoint_desc_right {tree : TraversalTree} {left right child : Nat}
    (separate : DisjointSubtrees tree left right) (descendant : Desc tree right child) :
    DisjointSubtrees tree left child := by
  intro node ⟨leftPath,childPath⟩
  exact separate node ⟨leftPath,descendant.trans childPath⟩

def PreviousEdge (tree : TraversalTree) (path : List Nat) (previous : Option Nat) : Prop :=
  ∀ current, path.head? = some current → ∀ before, previous = some before →
    ∃ valid : before < tree.nodes.size, tree.nodes[before].parent = some current

def deferredHeads (tree : TraversalTree) (mode : ChildrenVisitMode)
    (current : Nat) (previous : Option Nat) (isStart : Bool) : List Nat :=
  if !isStart || mode == .VisitChildrenOfAccessed then
    (tree.nodes[current]?.getD ⟨none,[]⟩).children.reverse.filter (fun child => previous != some child)
  else []

theorem roots_nil (tree : TraversalTree) (mode : ChildrenVisitMode) (previous : Option Nat) (isStart : Bool) :
    sourceForeignRootsGo tree mode [] previous isStart = [] := rfl

theorem roots_cons (tree : TraversalTree) (mode : ChildrenVisitMode)
    (current : Nat) (rest : List Nat) (previous : Option Nat) (isStart : Bool) :
    sourceForeignRootsGo tree mode (current::rest) previous isStart =
      deferredHeads tree mode current previous isStart ++ sourceForeignRootsGo tree mode rest (some current) false := rfl

theorem heads_data (tree : TraversalTree) (mode : ChildrenVisitMode) (current : Nat)
    (valid : current < tree.nodes.size) (previous : Option Nat) (isStart : Bool)
    (child : Nat) (member : child ∈ deferredHeads tree mode current previous isStart) :
    child ∈ tree.nodes[current].children ∧ previous ≠ some child := by
  unfold deferredHeads at member
  split at member
  · simp only [Array.getElem?_eq_getElem valid,Option.getD_some,List.mem_filter,List.mem_reverse] at member
    exact ⟨member.1,by simpa using member.2⟩
  · simp at member

structure FrontierData (tree : TraversalTree) (path : List Nat) (previous : Option Nat) (roots : List Nat) : Prop where
  bounded : ∀ root ∈ roots, root < tree.nodes.size
  separate : roots.Pairwise (DisjointSubtrees tree)
  offPath : ∀ root ∈ roots, ∀ node ∈ path, ¬ Desc tree root node
  offPrevious : ∀ before, previous = some before → ∀ root ∈ roots, DisjointSubtrees tree root before

theorem heads_separate (tree : TraversalTree) (forest : Forest tree) (mode : ChildrenVisitMode)
    (current : Nat) (valid : current < tree.nodes.size) (previous : Option Nat) (isStart : Bool) :
    (deferredHeads tree mode current previous isStart).Pairwise (DisjointSubtrees tree) := by
  have distinct : tree.nodes[current].children.reverse.Nodup :=
    List.pairwise_reverse.mpr ((forest.childrenDistinct current valid).imp (fun different => Ne.symm different))
  have full : tree.nodes[current].children.reverse.Pairwise (DisjointSubtrees tree) :=
    distinct.imp_of_mem (by
      intro left right leftMember rightMember different node
      exact siblings_disjoint forest current left right node valid
        (List.mem_reverse.mp leftMember) (List.mem_reverse.mp rightMember) different)
  unfold deferredHeads
  split
  · simp only [Array.getElem?_eq_getElem valid,Option.getD_some]
    exact full.filter _
  · exact .nil

theorem heads_off_path (tree : TraversalTree) (forest : Forest tree) (mode : ChildrenVisitMode)
    (current : Nat) (rest : List Nat) (spine : Spine tree (current::rest))
    (previous : Option Nat) (isStart : Bool) (child : Nat)
    (member : child ∈ deferredHeads tree mode current previous isStart)
    (node : Nat) (inPath : node ∈ current::rest) : ¬ Desc tree child node := by
  have currentValid := spine.bounded current (by simp)
  have childData := forest.childParent current currentValid child
    (heads_data tree mode current currentValid previous isStart child member).1
  intro descendant
  have lower := descendant.rank_le forest
  have upper := (spine.desc_head current rest node inPath).rank_le forest
  have strict := (forest.parents child childData.1 current childData.2).2
  omega

theorem heads_off_previous (tree : TraversalTree) (forest : Forest tree) (mode : ChildrenVisitMode)
    (current : Nat) (rest : List Nat) (valid : current < tree.nodes.size)
    (previous : Option Nat) (isStart : Bool) (edge : PreviousEdge tree (current::rest) previous)
    (before : Nat) (previousEq : previous = some before) (child : Nat)
    (member : child ∈ deferredHeads tree mode current previous isStart) : DisjointSubtrees tree child before := by
  have data := heads_data tree mode current valid previous isStart child member
  obtain ⟨beforeValid,beforeEdge⟩ := edge current rfl before previousEq
  have beforeMember := (forest.parentChild before beforeValid current beforeEdge).2
  have different : child ≠ before := by intro same; subst before; exact data.2 previousEq
  exact fun node => siblings_disjoint forest current child before node valid data.1 beforeMember different

theorem frontier_data (tree : TraversalTree) (forest : Forest tree) (mode : ChildrenVisitMode)
    (path : List Nat) (spine : Spine tree path) (previous : Option Nat) (isStart : Bool)
    (edge : PreviousEdge tree path previous) :
    FrontierData tree path previous (sourceForeignRootsGo tree mode path previous isStart) := by
  induction spine generalizing previous isStart with
  | nil =>
    rw [roots_nil]
    exact ⟨by simp, .nil, by simp, by simp⟩
  | @cons current rest valid tail pathEdge ih =>
    have nextEdge : PreviousEdge tree rest (some current) := by
      intro parent head before same
      have beforeEq : before = current := Option.some.inj same.symm
      subst before
      exact ⟨valid,pathEdge parent head⟩
    have later := ih (some current) false nextEdge
    rw [roots_cons]
    constructor
    · intro root member
      rcases List.mem_append.mp member with here | there
      · exact (forest.childParent current valid root (heads_data tree mode current valid previous isStart root here).1).1
      · exact later.bounded root there
    · apply List.pairwise_append.mpr
      refine ⟨heads_separate tree forest mode current valid previous isStart,later.separate,?_⟩
      intro child here upper there
      have childData := forest.childParent current valid child
        (heads_data tree mode current valid previous isStart child here).1
      exact disjoint_symm (disjoint_desc_right (later.offPrevious current rfl upper there)
        (.step (.refl current valid) childData.1 childData.2))
    · intro root member node inPath
      rcases List.mem_append.mp member with here | there
      · exact heads_off_path tree forest mode current rest (.cons valid tail pathEdge) previous isStart root here node inPath
      · rcases List.mem_cons.mp inPath with same | deeper
        · subst node
          exact fun fromRoot => later.offPrevious current rfl root there current ⟨fromRoot,.refl current valid⟩
        · exact later.offPath root there node deeper
    · intro before previousEq root member
      rcases List.mem_append.mp member with here | there
      · exact heads_off_previous tree forest mode current rest valid previous isStart edge before previousEq root here
      · obtain ⟨beforeValid,beforeEdge⟩ := edge current rfl before previousEq
        exact disjoint_desc_right (later.offPrevious current rfl root there)
          (.step (.refl current valid) beforeValid beforeEdge)

theorem initial_roots_data (tree : TraversalTree) (forest : Forest tree) (anchor : Nat)
    (valid : anchor < tree.nodes.size) (mode : ChildrenVisitMode) :
    FrontierData tree (tree.ancestorPath anchor) none (sourceForeignRoots tree (tree.ancestorPath anchor) mode) := by
  exact frontier_data tree forest mode _ (ancestors_spine tree forest tree.nodes.size anchor valid)
    none true (by intro current head before impossible; cases impossible)

end DuplicatePrefix.GeneralBorrowFrontier

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFrontier." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved general frontier dependency {dependency}"
