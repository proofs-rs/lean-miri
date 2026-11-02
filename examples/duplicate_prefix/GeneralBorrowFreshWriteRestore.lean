import duplicate_prefix.GeneralBorrowFreshTopology
import duplicate_prefix.GeneralBorrowFreshReuseTopology
import duplicate_prefix.GeneralBorrowAnchor
import duplicate_prefix.GeneralBorrowRelease

namespace DuplicatePrefix.GeneralBorrowFreshWriteRestore
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowTopology DuplicatePrefix.GeneralBorrowPresence
open DuplicatePrefix.GeneralBorrowAnchor DuplicatePrefix.GeneralBorrowPermissions
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

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
    | none => rfl
    | some earlier =>
      simp only [edge] at terminal ⊢
      have lastEq : (current :: sourceAncestorPath tree fuel earlier).getLast! =
          (sourceAncestorPath tree fuel earlier).getLast! := by
        simp only [List.getLast!_eq_getLast?_getD,List.getLast?_cons_of_ne_nil
          (GeneralBorrowTerminal.ancestors_nonempty tree fuel earlier)]
      rw [lastEq] at terminal
      rw [ih earlier terminal]

/-- Leaf append preserves the full production ancestor path of every old
anchor, accounting for the changed traversal fuel. -/
theorem append_path (before after : TraversalTree) (parent anchor : Nat)
    (extension : GeneralBorrowFreshTopology.Extension before after parent)
    (forest : GeneralBorrowForest.Forest before) (valid : anchor < before.nodes.size) :
    after.ancestorPath anchor = before.ancestorPath anchor := by
  unfold TraversalTree.ancestorPath
  rw [extension.length,GeneralBorrowFreshTopology.ancestors_old before after parent extension forest (before.nodes.size+1) anchor valid]
  exact terminal_step before before.nodes.size anchor (GeneralBorrowTerminal.ancestor_terminal before forest anchor valid)

private theorem reuse_avoids (tree : TraversalTree) (forest : GeneralBorrowForest.Forest tree)
    (index anchor : Nat) (valid : index < tree.nodes.size) (vacant : tree.nodes[index] = ⟨none,[]⟩)
    (anchorValid : anchor < tree.nodes.size) (different : anchor ≠ index) :
    index ∉ tree.ancestorPath anchor := by
  have closed : ParentClosed tree (fun position => position < tree.nodes.size ∧ position ≠ index) := by
    intro position known parent edge
    have original : tree.nodes[position].parent = some parent := by
      simpa only [nodeData,Array.getElem?_eq_getElem known.1,Option.getD_some] using edge
    refine ⟨(forest.parents position known.1 parent original).1,?_⟩
    intro same
    subst parent
    obtain ⟨bound,member⟩ := forest.parentChild position known.1 index original
    simp only [vacant,List.not_mem_nil] at member
  have present := ancestors_present tree (fun position => position < tree.nodes.size ∧ position ≠ index)
    closed tree.nodes.size anchor ⟨anchorValid,different⟩
  intro member
  exact (present index member).2 rfl

/-- Pure data transport for any old Write anchor. Only the added/reused child
may change its state: it is foreign, possible and unprotected. -/
theorem extension_owned (before after : NormalTreeState) (anchor child : Nat)
    (owned : AnchorOwned before anchor .Write)
    (valid : anchor < after.topology.nodes.size)
    (locations : after.locationStates.size = after.topology.nodes.size)
    (defaults : after.defaultStates.size = after.topology.nodes.size)
    (oldPosition : ∀ position, position < after.topology.nodes.size → position ≠ child → position < before.topology.nodes.size)
    (oldState : ∀ position, position < before.topology.nodes.size → position ≠ child → after.stateAt position = before.stateAt position)
    (oldProtection : ∀ position, position < before.topology.nodes.size → position ≠ child → after.protectedNodes.contains position = before.protectedNodes.contains position)
    (path : after.topology.ancestorPath anchor = before.topology.ancestorPath anchor)
    (foreignChild : child ∉ after.topology.ancestorPath anchor)
    (state : LocationState) (present : after.stateAt child = some state)
    (possible : state.possible = true) (released : after.protectedNodes.contains child = false) :
    AnchorOwned after anchor .Write := by
  refine ⟨valid,locations,defaults,?_⟩
  intro position bound
  by_cases same : position = child
  · subst position
    refine ⟨state,present,?_⟩
    simp only [AccessOwned,Owned,relation,foreignChild,↓reduceIte,released]
    exact ⟨possible,Or.inl rfl⟩
  · have oldBound := oldPosition position bound same
    obtain ⟨old,present,permission⟩ := owned.permissions position oldBound
    refine ⟨old,(oldState position oldBound same).trans present,?_⟩
    simpa only [relation,path,oldProtection position oldBound same] using permission

/-- Appending an unprotected shared child restores every pre-existing Write
anchor, including ancestors strictly above the child's immediate parent. -/
theorem append_owned (before after : NormalTreeState) (parent anchor : Nat)
    (extension : GeneralBorrowFreshTopology.Extension before.topology after.topology parent)
    (forest : GeneralBorrowForest.Forest before.topology) (owned : AnchorOwned before anchor .Write)
    (locations : after.locationStates.size = after.topology.nodes.size)
    (defaults : after.defaultStates.size = after.topology.nodes.size)
    (states : ∀ position, position < before.topology.nodes.size → after.stateAt position = before.stateAt position)
    (protections : ∀ position, position < before.topology.nodes.size → after.protectedNodes.contains position = before.protectedNodes.contains position)
    (state : LocationState) (present : after.stateAt before.topology.nodes.size = some state)
    (possible : state.possible = true) (released : after.protectedNodes.contains before.topology.nodes.size = false) :
    AnchorOwned after anchor .Write := by
  have path := append_path before.topology after.topology parent anchor extension forest owned.anchorValid
  apply extension_owned before after anchor before.topology.nodes.size owned
    (by rw [extension.length];have := owned.anchorValid;omega) locations defaults
    (by intro position bound different;rw [extension.length] at bound;omega)
    (by intro position bound different;exact states position bound)
    (by intro position bound different;exact protections position bound)
    path ?_ state present possible released
  rw [path]
  intro member
  have bound := (ancestors_data before.topology forest.rank forest.parents before.topology.nodes.size anchor owned.anchorValid).2 _ member
  exact Nat.lt_irrefl _ bound.1

/-- Replacing a vacant slot by an unprotected shared child has the same
Write-anchor restoration property. The existing anchor cannot be the vacant slot. -/
theorem reuse_owned (before after : NormalTreeState) (index parent anchor : Nat)
    (extension : GeneralBorrowFreshReuseTopology.Extension before.topology after.topology index parent)
    (forest : GeneralBorrowForest.Forest before.topology) (owned : AnchorOwned before anchor .Write)
    (different : anchor ≠ index)
    (locations : after.locationStates.size = after.topology.nodes.size)
    (defaults : after.defaultStates.size = after.topology.nodes.size)
    (states : ∀ position, position < before.topology.nodes.size → position ≠ index → after.stateAt position = before.stateAt position)
    (protections : ∀ position, position < before.topology.nodes.size → position ≠ index → after.protectedNodes.contains position = before.protectedNodes.contains position)
    (state : LocationState) (present : after.stateAt index = some state)
    (possible : state.possible = true) (released : after.protectedNodes.contains index = false) :
    AnchorOwned after anchor .Write := by
  have path : after.topology.ancestorPath anchor = before.topology.ancestorPath anchor := by
    unfold TraversalTree.ancestorPath
    rw [extension.length]
    exact GeneralBorrowFreshReuseTopology.ancestors_old before.topology after.topology index parent extension forest
      before.topology.nodes.size anchor owned.anchorValid different
  apply extension_owned before after anchor index owned
    (by rw [extension.length];exact owned.anchorValid) locations defaults
    (by intro position bound different;rw [extension.length] at bound;exact bound)
    states protections path ?_ state present possible released
  rw [path]
  exact reuse_avoids before.topology forest index anchor extension.valid extension.vacant owned.anchorValid different

private theorem required_possible (state : LocationState) (writable : Bool)
    (related : AccessRelatedness) (held : Bool) (owned : Required state writable related held) :
    state.possible = true := by
  cases writable <;> cases related <;> exact owned.1

/-- Restore an arbitrary mutable anchor from a mixed invariant. Multiple Frozen
ancestors may remain read-only: those leaving the local path must be unprotected.
Every node retained on the target local path must carry actual Write strength. -/
theorem mixed_owned (tree : NormalTreeState) (anchor : Nat)
    (valid : anchor < tree.topology.nodes.size)
    (locations : tree.locationStates.size = tree.topology.nodes.size)
    (defaults : tree.defaultStates.size = tree.topology.nodes.size)
    (writable : Nat → Bool) (beforeRelation : Nat → AccessRelatedness)
    (mixed : GeneralBorrowOwnership.Pointwise tree writable beforeRelation)
    (protections : List Nat)
    (weaken : ∀ position, protections.contains position = true → tree.protectedNodes.contains position = true)
    (localRetained : ∀ position, relation tree anchor position = .LocalAccess →
      beforeRelation position = .LocalAccess ∧ writable position = true)
    (leavingReleased : ∀ position, beforeRelation position = .LocalAccess →
      relation tree anchor position = .ForeignAccess → protections.contains position = false) :
    AnchorOwned {tree with protectedNodes := protections} anchor .Write := by
  refine ⟨valid,locations,defaults,?_⟩
  intro position bound
  obtain ⟨state,present,permission⟩ := mixed position (by rw [locations];exact bound)
  refine ⟨state,present,?_⟩
  change AccessOwned state .Write (relation tree anchor position) (protections.contains position)
  cases target : relation tree anchor position with
  | LocalAccess =>
    obtain ⟨beforeLocal,written⟩ := localRetained position target
    apply owned_release state .LocalAccess (tree.protectedNodes.contains position)
      (protections.contains position) (weaken position)
    simpa only [Required,written,↓reduceIte,beforeLocal] using permission
  | ForeignAccess =>
    cases earlier : beforeRelation position with
    | LocalAccess =>
      rw [leavingReleased position earlier target]
      exact ⟨required_possible state (writable position) (beforeRelation position)
        (tree.protectedNodes.contains position) permission,Or.inl rfl⟩
    | ForeignAccess =>
      apply owned_release state .ForeignAccess (tree.protectedNodes.contains position)
        (protections.contains position) (weaken position)
      cases label : writable position <;>
        simpa [Required,label,earlier,AccessOwned] using permission

end DuplicatePrefix.GeneralBorrowFreshWriteRestore
open Lean Elab Command in
run_cmd do
  for declaration in [``DuplicatePrefix.GeneralBorrowFreshWriteRestore.append_path,
      ``DuplicatePrefix.GeneralBorrowFreshWriteRestore.extension_owned,
      ``DuplicatePrefix.GeneralBorrowFreshWriteRestore.append_owned,
      ``DuplicatePrefix.GeneralBorrowFreshWriteRestore.reuse_owned,
      ``DuplicatePrefix.GeneralBorrowFreshWriteRestore.mixed_owned] do
    for dependency in (←collectAxioms declaration) do
      unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
        throwError "unapproved existing Write-anchor recovery dependency {dependency}"
