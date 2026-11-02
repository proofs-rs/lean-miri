import duplicate_prefix.CurrentCallResourceFnEntry
import duplicate_prefix.CurrentCallResourceInstallation

namespace DuplicatePrefix.CurrentCallBorrowIssuance
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- The SAME actual borrow witness issues its old parent and fresh child in
an actual installed world. No ownership reassignment, mode restriction, or
operation-success premise is introduced by this spatial transport. -/
theorem post {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (start amount : UInt64)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start amount)
    (tagEq : output.tag=tracker.global.nextPointerTag)
    (post : Before) (next : MachineHooks.BorrowState)
    (present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree))
    (rootTag : next.global.rootTag? id=tracker.global.rootTag? id) :
    SpatialDelegation post next id (W.allocation.setExtra output.child.tree)
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) W.pointer.grant ∧
    SpatialDelegation post next id (W.allocation.setExtra output.child.tree)
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child := by
  have vacant : W.allocation.extra.nodes.get child = none := by
    cases oldAt : W.allocation.extra.nodes.get child with
    | none => rfl
    | some old =>
      obtain ⟨changed,changedAt,changedTag,_,_,_⟩ := witness.oldNodes child old oldAt
      have same : changed = witness.node := Option.some.inj (changedAt.symm.trans witness.nodeAt)
      have oldTag : old.tag = output.tag := changedTag.symm.trans ((congrArg TreeNode.tag same).trans witness.tag)
      have older := GeneralBorrowParentTagInvariant.parent_below_fresh W.allocation.extra tracker.global runtime child old oldAt
      rw [oldTag,tagEq] at older
      exact False.elim (Nat.lt_irrefl _ (UInt64.lt_iff_toNat_lt.mp older))
  have parentIssued := CurrentCallResourceInstallation.spatial W.issued W.parents post next output.child.tree present rootTag
    witness.capacity witness.oldRoots witness.oldNodes child W.pointer.grant vacant
  have childIssued : SpatialDelegation post next id (W.allocation.setExtra output.child.tree)
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child := by
    have shape := witness.constructor
    cases provenance : W.pointer.value.provenance with
    | concrete supplied tag =>
      rw [provenance] at shape
      obtain ⟨parent,parentAt,_,_⟩ := W.binding
      obtain ⟨current,currentAt,_,_,_,_⟩ := witness.oldNodes W.pointer.grant parent parentAt
      apply SpatialDelegation.concrete parentIssued
      exact .step (.refl W.pointer.grant current currentAt) witness.node witness.nodeAt shape
    | wildcard =>
      rw [provenance] at shape
      obtain ⟨position,root,rootNode,rootSlot,rootAt,path⟩ := CandidateCurrentWindowAuthority.root_path output.child.tree witness.parents.graph child witness.node witness.nodeAt
      have rootEq : root = child := by
        cases path with
        | refl => rfl
        | @step predecessor target earlier node found edge =>
          have same : node = witness.node := Option.some.inj (found.symm.trans witness.nodeAt)
          rw [same,shape] at edge
          cases edge
      subst root
      have edge := S05ConcreteProtectedChildCompletion.child_edge W.precise.completion child W.pointer.grant
      obtain ⟨earlier,originRoot,newRoot,originNode,before,originSlot,newRootAt,originAt,exposed,older,originPath⟩ :=
        witness.parents.virtual position child rootSlot W.pointer.grant edge
      have same : newRoot = witness.node := Option.some.inj (newRootAt.symm.trans witness.nodeAt)
      exact SpatialDelegation.wildcard originNode newRoot earlier position originRoot parentIssued originAt exposed newRootAt
        (by rw [same];exact shape) older before originSlot rootSlot originPath edge
  exact ⟨parentIssued,childIssued⟩

end
end DuplicatePrefix.CurrentCallBorrowIssuance
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallBorrowIssuance" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual borrow issuance dependency {dependency}"
