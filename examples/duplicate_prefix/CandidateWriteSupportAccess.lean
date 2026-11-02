import duplicate_prefix.CandidateWriteSupportBoundary
import duplicate_prefix.S05DisabledLatentWildcardFailure

/-! Component completion regressions for the included wildcard postorder repair. -/

/-! Same-six-node raw visitor connection for the static candidate boundary.
No new raw fixture, ordinary-admissibility assertion, whole-call trace, or
Contract/Positive/final-safety negation is introduced. -/
namespace DuplicatePrefix.CandidateWriteSupportAccess
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open S05DiagnosticFnEntryRead GeneralBorrowNodeUpdate GeneralBorrowExposure
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
set_option cbv.maxSteps 1000000
set_option maxRecDepth 65536
set_option autoImplicit false
set_option linter.unusedSimpArgs false

private def afterCache : ExposedCache :=
  ⟨⟨#[some ⟨1,1⟩,some ⟨0,0⟩,some ⟨0,0⟩,some ⟨0,0⟩,some ⟨0,0⟩,some ⟨0,0⟩]⟩⟩
private def afterV : LocationTree :=
  {location with perms := location.perms.insert (ix 4) ⟨.Disabled,false,.Write⟩,exposedCache := afterCache}

private theorem cache_update : cache.updateExposure tree.nodes (ix 4) .Write .None = ⟨afterCache,.ok ()⟩ := by
  rw [GeneralBorrowExposureAncestorFold.update cache tree.nodes (Classical.choice CandidateSixNodeCertificate.graph.depth) (ix 4) v rfl .Write .None]
  rfl

private theorem record_v :
    (⟨.ReservedFrz false,false,.Read⟩ : LocationState).recordNewAccess .Write .ForeignAccess =
      .Recorded ⟨.ReservedFrz false,false,.Write⟩ := rfl
private theorem perform_v :
    (⟨.ReservedFrz false,false,.Write⟩ : LocationState).performAccess .Write .ForeignAccess false =
      .Success ⟨.Disabled,false,.Write⟩ ⟨.ReservedFrz false,.Disabled⟩ := rfl

/-- Revised visitor completion on the same six-node component. The old
failure proof is retained at the historical source link in this module. -/
theorem actual_completed :
    (tree.performWildcardAccessAt location (ix 1) (some (tag 4)) .Write {} true).status =
      .Completed := by cbv

theorem child_effects_retained :
    (tree.performWildcardAccessAt location (ix 1) (some (tag 4)) .Write {} true).location.perms.get (ix 4) =
      some ⟨.Disabled,false,.Write⟩ := by cbv

theorem child_cache_retained :
    (tree.performWildcardAccessAt location (ix 1) (some (tag 4)) .Write {} true).location.exposedCache = afterCache := by cbv

open CandidateStableCallOwnership CandidateCallBindings CandidateWriteSupportContext
open GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold

/-- The existing complete static candidate package and the same raw source
component completion coexist. This is not an ordinary-validity or whole-call result. -/
theorem joint_completed (seed : DuplicatePrefixCallSpecification.Before) :
    Interprets world CandidateSixNodeCertificate.held interpretation ∧
    Claims interpretation call ∧
    Bindings (CandidateWriteSupportBoundary.actualBefore seed) world CandidateSixNodeCertificate.held interpretation call argument 2 place ∧
    GeneralBorrowStructuralHistoryState.GraphState sourceAllocation.extra ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceAllocation.extra ∧
    GeneralBorrowStructuralHistoryState.GraphState returnAllocation.extra ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder returnAllocation.extra ∧
    (∀ support, S05LiveSubtreeCacheSoundness.Soundness sourceAllocation.extra
      S05DiagnosticFnEntryRead.location CandidateSixNodeCertificate.held support) ∧
    (¬ ∃ area : GeneralBorrowWildcardControlStack.Support sourceAllocation.extra (S05DiagnosticFnEntryRead.ix 1),
      ∀ query node, area.contains query → sourceAllocation.extra.nodes.get query = some node →
      ∀ witness witnessNode, sourceAllocation.extra.nodes.get witness = some witnessNode →
      witnessNode.isExposed = true →
      query ∈ walk sourceAllocation.extra.nodes (sourceAllocation.extra.nodes.size+1) witness →
      supports (effective S05DiagnosticFnEntryRead.location CandidateSixNodeCertificate.held witness witnessNode) .Write = true →
      (RawState S05DiagnosticFnEntryRead.location query node).permission ≠ .Disabled ∧
      (RawState S05DiagnosticFnEntryRead.location query node).permission ≠ .Frozen) ∧
    (¬ ∃ area : GeneralBorrowWildcardControlStack.Support sourceAllocation.extra (S05DiagnosticFnEntryRead.ix 1),
      S05WriteCacheContributorOwnership.SkipStable sourceAllocation.extra
        S05DiagnosticFnEntryRead.location CandidateSixNodeCertificate.held
        (some (S05DiagnosticFnEntryRead.tag 4)) area.contains) ∧
    (sourceAllocation.extra.performWildcardAccessAt location (ix 1)
      (some (tag 4)) .Write CandidateSixNodeCertificate.held true).status = .Completed := by
  obtain ⟨interprets,claims,bindings,sourceGraph,sourceOrder,returnGraph,returnOrder,sound,noLive,noStable⟩ :=
    CandidateWriteSupportBoundary.joint seed
  exact ⟨interprets,claims,bindings,sourceGraph,sourceOrder,returnGraph,returnOrder,sound,noLive,noStable,actual_completed⟩

end DuplicatePrefix.CandidateWriteSupportAccess
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateWriteSupportAccess." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved same-source access dependency {dependency}"
