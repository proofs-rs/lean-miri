import duplicate_prefix.CurrentCallResourceInstallation

namespace DuplicatePrefix.CurrentCallAllocationLicense
open Miri Miri.Input Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

/-! Spatial allocation licenses are insensitive to stored bytes, initialization
and provenance-map changes. Presence always names the ACTUAL updated allocation;
byte validity, initialization and DirectInput remain separate obligations. -/

theorem capability {before : Before} {tracker : MachineHooks.BorrowState} {id : AllocId}
    {allocation : Allocation Provenance BorrowTree}
    (old : AllocationCapability before tracker id allocation)
    (post : Before) (next : MachineHooks.BorrowState) (updated : Allocation Provenance BorrowTree)
    (present : Present (ActualWorld post) id updated)
    (rootTag : next.global.rootTag? id = tracker.global.rootTag? id)
    (lenEq : updated.len = allocation.len) (byteSizeEq : updated.byteSize = allocation.byteSize)
    (capacity : updated.extra.locations.size = allocation.extra.locations.size)
    (roots : ∀ (position : Nat) (root : UniIndex),allocation.extra.roots[position]? = some root → updated.extra.roots[position]? = some root)
    (metadata : ∀ index node,allocation.extra.nodes.get index = some node →
      ∃ changed,updated.extra.nodes.get index = some changed ∧ changed.tag = node.tag ∧ changed.parent = node.parent ∧
        changed.isExposed = node.isExposed ∧ changed.defaultInitialPermission = node.defaultInitialPermission) :
    AllocationCapability post next id updated := by
  refine ⟨present,by rw [lenEq,byteSizeEq];exact old.extent,by rw [byteSizeEq];exact capacity.trans old.treeExtent,roots 0 allocationRoot old.rootSlot,?_⟩
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


theorem spatial {before : Before} {tracker : MachineHooks.BorrowState} {id : AllocId}
    {allocation : Allocation Provenance BorrowTree} {completion : Completion} {grant : UniIndex}
    (old : SpatialDelegation before tracker id allocation completion grant)
    (post : Before) (next : MachineHooks.BorrowState) (updated : Allocation Provenance BorrowTree)
    (present : Present (ActualWorld post) id updated)
    (rootTag : next.global.rootTag? id = tracker.global.rootTag? id)
    (lenEq : updated.len = allocation.len) (byteSizeEq : updated.byteSize = allocation.byteSize)
    (capacity : updated.extra.locations.size = allocation.extra.locations.size)
    (roots : ∀ (position : Nat) (root : UniIndex),allocation.extra.roots[position]? = some root → updated.extra.roots[position]? = some root)
    (metadata : ∀ index node,allocation.extra.nodes.get index = some node →
      ∃ changed,updated.extra.nodes.get index = some changed ∧ changed.tag = node.tag ∧ changed.parent = node.parent ∧
        changed.isExposed = node.isExposed ∧ changed.defaultInitialPermission = node.defaultInitialPermission)
    (newC : Completion)
    (edges : ∀ (root origin : UniIndex),completion.parents[root.toNat]? = some (some origin) →
      newC.parents[root.toNat]? = some (some origin)) :
    SpatialDelegation post next id updated newC grant := by
  induction old with
  | allocated cap => exact .allocated (capability cap post next updated present rootTag lenEq byteSizeEq capacity roots metadata)
  | concrete issued path ih => exact .concrete ih (paths metadata path)
  | @wildcard origin root originNode rootNode earlier position originRoot issued originAt exposed rootAt parentless older earlierPosition earlierAt rootSlot path edge ih =>
    obtain ⟨changedOrigin,changedOriginAt,originTag,_,originExposure,_⟩ := metadata origin originNode originAt
    obtain ⟨changedRoot,changedRootAt,rootNodeTag,rootParent,_,_⟩ := metadata root rootNode rootAt
    exact .wildcard changedOrigin changedRoot earlier position originRoot ih changedOriginAt
      (originExposure.trans exposed) changedRootAt (rootParent.trans parentless)
      (by rw [originTag,rootNodeTag]; exact older) earlierPosition (roots earlier originRoot earlierAt)
      (roots position root rootSlot) (paths metadata path) (edges root origin edge)

end DuplicatePrefix.CurrentCallAllocationLicense
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallAllocationLicense.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved actual allocation license dependency {dependency}"
