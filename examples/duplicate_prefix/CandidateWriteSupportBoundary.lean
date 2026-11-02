import duplicate_prefix.CandidateWriteSupportContext

/-! Actual-state bindings for the SAME static ownership witness. A seed supplies
unused machine fields; overwriting these fields is not a machine-wellformedness,
history, ordinary-input or execution certificate. The candidate remains unadopted.
-/
namespace DuplicatePrefix.CandidateWriteSupportBoundary
open Miri Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter
open CandidateStableCallOwnership CandidateCallBindings CandidateWriteSupportContext
open Miri.TreeBorrows.Tree GeneralBorrowExposureCardinality GeneralBorrowExposureAncestorFold
open GeneralBorrowExposedNonleafPrimaryPath
set_option autoImplicit false
set_option maxRecDepth 65536
set_option linter.unusedSimpArgs false

/-- Only the current data inspected by the binding relation is replaced. -/
def actualBefore (seed : DuplicatePrefixCallSpecification.Before) :
    DuplicatePrefixCallSpecification.Before :=
  { seed with
    memory := {seed.memory with live :=
      #[(sourceId,⟨.stack,sourceAllocation⟩),(returnId,⟨.stack,returnAllocation⟩)]}
    borrowTracker := some ⟨{nextPointerTag := S05DiagnosticFnEntryRead.tag 8, rootPointerTags := #[(sourceId,S05DiagnosticFnEntryRead.tag 1),(returnId,S05DiagnosticFnEntryRead.tag 7)]},.Default⟩
    user := {seed.user with addresses := {seed.user.addresses with
      baseAddr := #[⟨sourceId,4096⟩,⟨returnId,8192⟩]}} }

theorem world_eq (seed : DuplicatePrefixCallSpecification.Before) :
    world = actualWorld (actualBefore seed) := by
  simp [world,actualWorld,actualBefore]

theorem source_window (seed : DuplicatePrefixCallSpecification.Before) :
    WindowBinding (actualBefore seed) sourcePointer sourceId 0 2 := by
  refine ⟨⟨.stack,sourceAllocation⟩,4096,?_⟩
  change _
  simp only [actualBefore,sourcePointer,returnPointer]
  refine ⟨rfl,rfl,?_⟩
  decide +kernel

theorem return_window (seed : DuplicatePrefixCallSpecification.Before) :
    WindowBinding (actualBefore seed) returnPointer returnId 0 1 := by
  refine ⟨⟨.stack,returnAllocation⟩,8192,?_⟩
  change _
  simp only [actualBefore,sourcePointer,returnPointer]
  refine ⟨rfl,rfl,?_⟩
  decide +kernel

/-- Exact loan indices and exact pointer values; no equality-of-bits argument
identifies unrelated program copies or certifies their lifetimes. -/
theorem bindings (seed : DuplicatePrefixCallSpecification.Before) :
    Bindings (actualBefore seed) world CandidateSixNodeCertificate.held
      interpretation call argument 2 place := by
  refine ⟨world_eq seed,⟨_,rfl,rfl⟩,rfl,?_,?_⟩
  · right
    refine ⟨by decide,sourcePointer,rfl,?_⟩
    exact ⟨⟨0,none,0⟩,⟨sourceId,sourcePointer,S05DiagnosticFnEntryRead.ix 5⟩,
      rfl,rfl,rfl,rfl,source_window seed⟩
  · refine ⟨rfl,returnPointer,rfl,?_⟩
    exact ⟨⟨1,none,0⟩,⟨returnId,returnPointer,S05DiagnosticFnEntryRead.ix 0⟩,
      rfl,rfl,rfl,rfl,return_window seed⟩

/-- Static non-implication witness for a formation route: all candidate clauses
and actual bindings coexist with failure of blanket raw Write-live. This is
conditional only on supplying a seed value, not a valid-state/NoUB counterexample. -/
theorem joint (seed : DuplicatePrefixCallSpecification.Before) :
    Interprets world CandidateSixNodeCertificate.held interpretation ∧
    Claims interpretation call ∧
    Bindings (actualBefore seed) world CandidateSixNodeCertificate.held interpretation call argument 2 place ∧
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
        (some (S05DiagnosticFnEntryRead.tag 4)) area.contains) := by
  refine ⟨CandidateWriteSupportContext.interprets,CandidateWriteSupportContext.claims,
    bindings seed,CandidateSixNodeCertificate.graph,CandidateSixNodeCertificate.order,
    CandidateWriteSupportContext.return_graph,CandidateWriteSupportContext.return_order,
    CandidateSixNodeCertificate.sound,?_,?_⟩
  · rintro ⟨area,live⟩
    exact CandidateSixNodeCertificate.no_area_write_live area live
  · rintro ⟨area,stable⟩
    exact CandidateSixNodeCertificate.no_area_skip_stable area stable

end DuplicatePrefix.CandidateWriteSupportBoundary

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateWriteSupportBoundary." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved actual-state witness dependency {dependency}"
