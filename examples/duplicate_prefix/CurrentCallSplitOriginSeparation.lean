import duplicate_prefix.CurrentCallSplitOriginTrace
import duplicate_prefix.CurrentCallNoUniformOrigin
namespace DuplicatePrefix.CurrentCallSplitOriginSeparation
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CandidateCurrentGrantResources CurrentCallResourceNormalization
open CurrentCallSplitOriginTrace
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The SAME actual chained final tree admits no single completed issued origin
for V's whole two-byte exclusive content. Any actual backing may be installed;
no fictitious machine or assumed final operation success is supplied. -/
theorem no_uniform_origin (before : Before) (tracker : MachineHooks.BorrowState) (id : AllocId)
    (backing : Allocation Provenance BorrowTree) :
    ¬∃ completion,ParentInterpretation (backing.setExtra finalWrite.tree).extra completion ∧
      SpatialDelegation before tracker id (backing.setExtra finalWrite.tree) completion (ix 3) ∧
      ∀ byte,byte<2 → Embeds (backing.setExtra finalWrite.tree) {} completion (ix 3) byte .exclusive := by
  obtain ⟨firstAt,secondAt,grantAt,_,_,parentless,notRoot⟩ := node_endpoints
  obtain ⟨leftMember,rightMember,leftStart,leftStop,rightStart,rightStop,firstDisabled,secondDisabled⟩ := segment_endpoints
  apply CurrentCallNoUniformOrigin.two_exposed before tracker id (backing.setExtra finalWrite.tree) {} (ix 3) (finalNode 3)
    grantAt parentless notRoot (ix 1) (ix 2) (finalNode 1) (finalNode 2) firstAt secondAt exposed_only_a_or_b
    leftSegment rightSegment leftMember rightMember
  · rw [leftStart];exact Nat.le_refl 0
  · rw [leftStop];decide
  · rw [rightStart];exact Nat.le_refl 1
  · rw [rightStop];decide
  · exact firstDisabled
  · exact secondDisabled

/-- All eleven actual core steps complete, but the resulting V is not covered
by this candidate's one-origin allocation-wide issuance/content combination.
This is neither an Ordinary-input counterexample nor a UB/whole-call claim. -/
theorem completed_trace_separation (before : Before) (tracker : MachineHooks.BorrowState) (id : AllocId)
    (backing : Allocation Provenance BorrowTree) :
    (readA.status=.Completed ∧ a.outcome=.ok () ∧ readB.status=.Completed ∧ b.outcome=.ok () ∧
      writeA.status=.Completed ∧ writeB.status=.Completed ∧ exposeA.outcome=.ok () ∧ exposeB.outcome=.ok () ∧
      wildcardRead.status=.Completed ∧ v.outcome=.ok () ∧ finalWrite.status=.Completed) ∧
    ¬∃ completion,ParentInterpretation (backing.setExtra finalWrite.tree).extra completion ∧
      SpatialDelegation before tracker id (backing.setExtra finalWrite.tree) completion (ix 3) ∧
      ∀ byte,byte<2 → Embeds (backing.setExtra finalWrite.tree) {} completion (ix 3) byte .exclusive :=
  ⟨operations_complete,no_uniform_origin before tracker id backing⟩

end
end DuplicatePrefix.CurrentCallSplitOriginSeparation
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallSplitOriginSeparation" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved actual split-origin coupling dependency {dependency}"
