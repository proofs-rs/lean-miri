import duplicate_prefix.CurrentCallResourceNormalization
import duplicate_prefix.S05ConcreteProtectedChildCompletion

namespace DuplicatePrefix.CurrentCallResourceInstallation
open Miri Miri.Input Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- The actual installed allocation supplies current presence. Tree-only
installation retains the old extent license and canonical root/cache data;
this statement is not an execution or family-history certificate. -/
theorem capability {before : Before} {tracker : MachineHooks.BorrowState} {id : AllocId}
    {allocation : Allocation Provenance BorrowTree}
    (old : AllocationCapability before tracker id allocation)
    (post : Before) (next : MachineHooks.BorrowState) (afterTree : BorrowTree)
    (present : Present (ActualWorld post) id (allocation.setExtra afterTree))
    (rootTag : next.global.rootTag? id = tracker.global.rootTag? id)
    (capacity : afterTree.locations.size = allocation.extra.locations.size)
    (roots : ∀ (position : Nat) (root : UniIndex),allocation.extra.roots[position]? = some root → afterTree.roots[position]? = some root)
    (metadata : ∀ index node,allocation.extra.nodes.get index = some node →
      ∃ changed,afterTree.nodes.get index = some changed ∧ changed.tag = node.tag ∧ changed.parent = node.parent ∧
        changed.isExposed = node.isExposed ∧ changed.defaultInitialPermission = node.defaultInitialPermission) :
    AllocationCapability post next id (allocation.setExtra afterTree) := by
  refine ⟨present,old.extent,capacity.trans old.treeExtent,roots 0 allocationRoot old.rootSlot,?_⟩
  obtain ⟨node,found,parentless,disabled,cached⟩ := old.rootNode
  obtain ⟨changed,changedAt,tag,parent,_,permission⟩ := metadata allocationRoot node found
  refine ⟨changed,changedAt,parent.trans parentless,permission.trans disabled,?_⟩
  rw [tag]
  exact rootTag.trans cached

private theorem paths {before after : BorrowTree}
    (metadata : ∀ index node,before.nodes.get index = some node →
      ∃ changed,after.nodes.get index = some changed ∧ changed.tag = node.tag ∧ changed.parent = node.parent ∧
        changed.isExposed = node.isExposed ∧ changed.defaultInitialPermission = node.defaultInitialPermission)
    {root query : UniIndex} (path : Path before root query) : Path after root query := by
  induction path with
  | refl node found =>
    obtain ⟨changed,present,_⟩ := metadata _ node found
    exact .refl _ changed present
  | step earlier node found edge ih =>
    obtain ⟨changed,present,_,parent,_⟩ := metadata _ node found
    exact .step ih changed present (parent.trans edge)

/-- Previously issued grants move to the actual post-heap allocation with
one real fresh-slot parent extension. Old physical paths and already exposed
virtual origins remain fixed; no new family/copy correlation is asserted. -/
theorem spatial {before : Before} {tracker : MachineHooks.BorrowState} {id : AllocId}
    {allocation : Allocation Provenance BorrowTree} {completion : Completion} {grant : UniIndex}
    (old : SpatialDelegation before tracker id allocation completion grant)
    (model : ParentInterpretation allocation.extra completion)
    (post : Before) (next : MachineHooks.BorrowState) (afterTree : BorrowTree)
    (present : Present (ActualWorld post) id (allocation.setExtra afterTree))
    (rootTag : next.global.rootTag? id = tracker.global.rootTag? id)
    (capacity : afterTree.locations.size = allocation.extra.locations.size)
    (roots : ∀ (position : Nat) (root : UniIndex),allocation.extra.roots[position]? = some root → afterTree.roots[position]? = some root)
    (metadata : ∀ index node,allocation.extra.nodes.get index = some node →
      ∃ changed,afterTree.nodes.get index = some changed ∧ changed.tag = node.tag ∧ changed.parent = node.parent ∧
        changed.isExposed = node.isExposed ∧ changed.defaultInitialPermission = node.defaultInitialPermission)
    (child parent : UniIndex) (vacant : allocation.extra.nodes.get child = none) :
    SpatialDelegation post next id (allocation.setExtra afterTree)
      (S05ConcreteProtectedChildCompletion.extend completion child parent) grant := by
  induction old with
  | allocated cap => exact .allocated (capability cap post next afterTree present rootTag capacity roots metadata)
  | concrete issued path ih => exact .concrete ih (paths metadata path)
  | @wildcard origin root originNode rootNode earlier position originRoot issued originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge ih =>
    obtain ⟨changedOrigin,changedOriginAt,originTag,_,originExposure,_⟩ := metadata origin originNode originAt
    obtain ⟨changedRoot,changedRootAt,rootNodeTag,rootParent,_,_⟩ := metadata root rootNode rootAt
    have different : root ≠ child := by
      intro same
      obtain ⟨node,live⟩ := (model.edgeLive root origin edge).1
      rw [same,vacant] at live
      cases live
    have bound : root.toNat < completion.parents.size := by
      by_cases fits : root.toNat < completion.parents.size
      · exact fits
      · rw [Array.getElem?_eq_none (Nat.le_of_not_lt fits)] at edge
        cases edge
    have retained := (S05ConcreteProtectedChildCompletion.old_parent completion child parent root different bound).trans edge
    exact .wildcard changedOrigin changedRoot earlier position originRoot ih changedOriginAt
      (originExposure.trans exposed) changedRootAt (rootParent.trans parentless)
      (by rw [originTag,rootNodeTag]; exact older) earlierPosition (roots earlier originRoot earlierAt)
      (roots position root rootSlot) (paths metadata path) retained

/-- Actual tree-only installation also transports old issuance across a
finite parent-map frame, including an unassigned fresh zero root. The immediate
constructor consumer derives preservation of old virtual edges from its real
parent-map operation; no new initial issuance clause is introduced. -/
theorem spatial_frame {before : Before} {tracker : MachineHooks.BorrowState} {id : AllocId}
    {allocation : Allocation Provenance BorrowTree} {completion : Completion} {grant : UniIndex}
    (old : SpatialDelegation before tracker id allocation completion grant)
    (post : Before) (next : MachineHooks.BorrowState) (afterTree : BorrowTree)
    (present : Present (ActualWorld post) id (allocation.setExtra afterTree))
    (rootTag : next.global.rootTag? id = tracker.global.rootTag? id)
    (capacity : afterTree.locations.size = allocation.extra.locations.size)
    (roots : ∀ (position : Nat) (root : UniIndex),allocation.extra.roots[position]? = some root → afterTree.roots[position]? = some root)
    (metadata : ∀ index node,allocation.extra.nodes.get index = some node →
      ∃ changed,afterTree.nodes.get index = some changed ∧ changed.tag = node.tag ∧ changed.parent = node.parent ∧
        changed.isExposed = node.isExposed ∧ changed.defaultInitialPermission = node.defaultInitialPermission)
    (newC : Completion)
    (edges : ∀ (root origin : UniIndex),completion.parents[root.toNat]? = some (some origin) →
      newC.parents[root.toNat]? = some (some origin)) :
    SpatialDelegation post next id (allocation.setExtra afterTree) newC grant := by
  induction old with
  | allocated cap => exact .allocated (capability cap post next afterTree present rootTag capacity roots metadata)
  | concrete issued path ih => exact .concrete ih (paths metadata path)
  | @wildcard origin root originNode rootNode earlier position originRoot issued originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge ih =>
    obtain ⟨changedOrigin,changedOriginAt,originTag,_,originExposure,_⟩ := metadata origin originNode originAt
    obtain ⟨changedRoot,changedRootAt,rootNodeTag,rootParent,_,_⟩ := metadata root rootNode rootAt
    exact .wildcard changedOrigin changedRoot earlier position originRoot ih changedOriginAt
      (originExposure.trans exposed) changedRootAt (rootParent.trans parentless)
      (by rw [originTag,rootNodeTag]; exact older) earlierPosition (roots earlier originRoot earlierAt)
      (roots position root rootSlot) (paths metadata path) (edges root origin edge)

end DuplicatePrefix.CurrentCallResourceInstallation

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceInstallation" then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current installation dependency {dependency}"
