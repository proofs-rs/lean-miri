import duplicate_prefix.CurrentCallResourceFnEntry
import duplicate_prefix.CurrentCallBorrowIssuance
namespace DuplicatePrefix.CurrentCallResourceChildWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources
open CurrentCallResourceNormalization GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- These appended loan/family slots are technical backend indices only. In
particular the appended loan index is NOT claimed vacant in the content
fragment, and its parent field is NOT a semantic delegation of `.ret`. -/
private def childData {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) : Identities :=
  {data with interpretation := {data.interpretation with
    pointers := data.interpretation.pointers.push (CurrentCallResourceFnEntry.child_pointer W output.tag child)
    loans := data.interpretation.loans.push ⟨data.interpretation.pointers.size,some owner,W.loan.depth+1⟩
    precise := (data.interpretation.precise.map (fun pair => if pair.1 = id then
      (id,{pair.2 with completion := S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant}) else pair))}}

private def childView {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (start amount : UInt64)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start amount)
    (post : Before)
    (present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree))
    (issued : SpatialDelegation post ⟨output.global,tracker.retagMode⟩ id (W.allocation.setExtra output.child.tree)
      (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant) child) :
    UniformWindow post ⟨output.global,tracker.retagMode⟩ (childData W output child)
      data.interpretation.loans.size id offset length .ret where
  loan := ⟨data.interpretation.pointers.size,some owner,W.loan.depth+1⟩
  pointer := CurrentCallResourceFnEntry.child_pointer W output.tag child
  allocation := W.allocation.setExtra output.child.tree
  precise := {W.precise with completion := S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant}
  loanAt := by simp only [childData,Array.getElem?_push,ite_true]
  pointerAt := by simp only [childData,Array.getElem?_push,ite_true]
  pointerId := rfl
  present := present
  preciseAt := by
    change (id,{W.precise with completion := S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant}) ∈
      (data.interpretation.precise.map (fun pair => if pair.1 = id then
        (id,{pair.2 with completion := S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant}) else pair)).toList
    apply Array.mem_toList_iff.mpr
    apply Array.mem_map.mpr
    exact ⟨(id,W.precise),Array.mem_toList_iff.mp W.preciseAt,by simp only [ite_true]⟩
  binding := witness.binding
  issued := issued
  parents := witness.parents
  window := by
    intro byte inside
    obtain ⟨bound,embedding⟩ := witness.window byte inside
    refine ⟨?_,?_⟩
    · simpa only [Allocation.len,Allocation.setExtra,Allocation.mapExtra] using bound
    · simpa [demandOf,CurrentCallResourceFnEntry.child_pointer] using embedding

/-- Actual child resources supply the concrete Write used by Bool activation.
This is not an active-parent content claim or a new ownership transition. -/
theorem child_write_contract {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (start amount : UInt64)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start amount)
    (tag : output.tag = tracker.global.nextPointerTag)
    (post : Before) (present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree))
    (rootTag : output.global.rootTag? id = tracker.global.rootTag? id)
    (actual : ActualRealized (ActualWorld post) output.global.protectedTags)
    (distinct : output.child.tree.roots.toList.Nodup) (short : output.child.tree.nodes.size < 65536)
    (startEq : start.toNat = offset) (amountEq : amount.toNat = length)
    (bounds : start.toNat+amount.toNat ≤ output.child.tree.locations.size.bytes.toNat)
    (visit : ChildrenVisitMode) :
    GeneralBorrowConcreteRangeInvariant.Contract output.child.tree
      (S05CompletedAncestryReadMutable.Authority output.child.tree
        (S05ConcreteProtectedChildCompletion.extend W.precise.completion child W.pointer.grant)
        output.global.protectedTags child)
      (fun location => GeneralBorrowExposureCardinality.LocationCoherent output.child.tree location output.global.protectedTags ∧
        GeneralBorrowLocationSifaConsistency.Profile output.child.tree location output.global.protectedTags ∧
        GeneralBorrowSnapshotReadRuntime.GlobalPossible output.child.tree location)
      (fun _ _ => True) start (start+amount)
      (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes amount)
        .Write output.global.protectedTags visit) := by
  have issued := (CurrentCallBorrowIssuance.post W runtime output child start amount witness tag post
    ⟨output.global,tracker.retagMode⟩ present rootTag).2
  let current := childView W output child start amount witness post present issued
  obtain ⟨geometry⟩ := CurrentCallResourceNormalization.geometry current actual (by simp [demandOf])
  have endFits : start.toNat+amount.toNat < 2^64 := Nat.lt_of_le_of_lt bounds (UInt64.toNat_lt output.child.tree.locations.size.bytes)
  have endEq : (start+amount).toNat = start.toNat+amount.toNat := by
    simp only [UInt64.toNat_add,Nat.mod_eq_of_lt endFits]
  have contract := CurrentCallResourceAccess.write_range current geometry (by simp [demandOf]) distinct short witness.runtime.formed.well
    (fun position valid => ⟨witness.runtime.coherent position valid,witness.runtime.formed.profile position valid,witness.runtime.possible position valid⟩)
    (Size.ofBytes start) (Size.ofBytes amount) start (start+amount) (by omega) (by omega) bounds (Nat.le_refl _) (Nat.le_refl _) visit
  exact contract

/-- Existing completion-only API, projected from the same actual Write contract. -/
theorem child_write {before tracker data owner id offset length mode}
    (W : UniformWindow before tracker data owner id offset length mode)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts W.allocation.extra tracker.global)
    (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (start amount : UInt64)
    (witness : CurrentCallResourceFnEntry.BorrowWitness W output child start amount)
    (tag : output.tag = tracker.global.nextPointerTag)
    (post : Before) (present : Present (ActualWorld post) id (W.allocation.setExtra output.child.tree))
    (rootTag : output.global.rootTag? id = tracker.global.rootTag? id)
    (actual : ActualRealized (ActualWorld post) output.global.protectedTags)
    (distinct : output.child.tree.roots.toList.Nodup) (short : output.child.tree.nodes.size < 65536)
    (startEq : start.toNat = offset) (amountEq : amount.toNat = length)
    (bounds : start.toNat+amount.toNat ≤ output.child.tree.locations.size.bytes.toNat)
    (visit : ChildrenVisitMode) :
    (output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes start) (Size.ofBytes amount)
      .Write output.global.protectedTags visit).status = .Completed := by
  exact (child_write_contract W runtime output child start amount witness tag post present rootTag actual
    distinct short startEq amountEq bounds visit).completed

end
end DuplicatePrefix.CurrentCallResourceChildWrite
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallResourceChildWrite" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved resource-child-write dependency {dependency}"
