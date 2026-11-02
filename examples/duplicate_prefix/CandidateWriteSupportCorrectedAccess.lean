import duplicate_prefix.CandidateWriteSupportBoundary
import duplicate_prefix.S05DisabledLatentWildcardFailure

/-! Component completion regressions for the included wildcard postorder repair. -/

/-! Revised six-node component regression, retaining the default-SIFA and
accessed-field corrections. Historical failure is tied to the old revision,
not asserted for the repaired visitor. No whole-call Result is established. -/
namespace DuplicatePrefix.CandidateWriteSupportCorrectedAccess
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open S05DiagnosticFnEntryRead GeneralBorrowNodeUpdate GeneralBorrowExposure
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail
set_option cbv.maxSteps 1000000
set_option maxRecDepth 65536
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
/-- D creation can weaken its parent's default SIFA to Read. -/
def correctedA : TreeNode := {a with defaultInitialSifa := .Read}
def correctedTree : BorrowTree := {S05DiagnosticFnEntryRead.tree with nodes := {data := #[some original,some correctedA,some d,some b,some v,some w]}}

/-- The parent Read used to create D marks the materialized Cell accessed. -/
def correctedLocation : LocationTree := {location with perms := location.perms.insert (ix 1) ⟨.Cell,true,.Write⟩}
private def afterCache : ExposedCache :=
  ⟨⟨#[some ⟨1,1⟩,some ⟨0,0⟩,some ⟨0,0⟩,some ⟨0,0⟩,some ⟨0,0⟩,some ⟨0,0⟩]⟩⟩
private def afterV : LocationTree :=
  {correctedLocation with perms := correctedLocation.perms.insert (ix 4) ⟨.Disabled,false,.Write⟩,exposedCache := afterCache}

private theorem cache_update : cache.updateExposure correctedTree.nodes (ix 4) .Write .None = ⟨afterCache,.ok ()⟩ := by
  unfold ExposedCache.updateExposure
  simp only [show (WildcardAccessLevel.Write == WildcardAccessLevel.None) = false from rfl, Bool.false_eq_true, ↓reduceIte, Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  let c1 : ExposedCache := ⟨⟨#[some ⟨1,1⟩,some ⟨1,1⟩,some ⟨1,1⟩,some ⟨0,0⟩,some ⟨0,0⟩,some ⟨0,0⟩]⟩⟩
  let c2 : ExposedCache := ⟨⟨#[some ⟨1,1⟩,some ⟨1,1⟩,some ⟨0,0⟩,some ⟨0,0⟩,some ⟨0,0⟩,some ⟨0,0⟩]⟩⟩
  have s1 : scan () (cache,some (ix 4),0,Except.ok (),true) = .yield (c1,some (ix 2),1,Except.ok (),true) := by
    dsimp [scan,c1,c2,correctedTree,correctedA,cache,afterCache,S05DiagnosticFnEntryRead.tree,a,d,b,v,w,original,tag,ix,UniIndex.toNat,UniValMap.get,UniValMap.size,UniValMap.insert,UniValMap.extendTo]
    apply congrArg ForInStep.yield
    decide +kernel
  have s2 : scan () (c1,some (ix 2),1,Except.ok (),true) = .yield (c2,some (ix 1),2,Except.ok (),true) := by
    dsimp [scan,c1,c2,correctedTree,correctedA,cache,afterCache,S05DiagnosticFnEntryRead.tree,a,d,b,v,w,original,tag,ix,UniIndex.toNat,UniValMap.get,UniValMap.size,UniValMap.insert,UniValMap.extendTo]
    apply congrArg ForInStep.yield
    decide +kernel
  have s3 : scan () (c2,some (ix 1),2,Except.ok (),true) = .yield (afterCache,none,3,Except.ok (),false) := by
    dsimp [scan,c1,c2,correctedTree,correctedA,cache,afterCache,S05DiagnosticFnEntryRead.tree,a,d,b,v,w,original,tag,ix,UniIndex.toNat,UniValMap.get,UniValMap.size,UniValMap.insert,UniValMap.extendTo]
    apply congrArg ForInStep.yield
    decide +kernel
  have stop : scan () (afterCache,none,3,Except.ok (),false) = .done (afterCache,none,3,Except.ok (),false) := by rfl
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s1,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s2,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [s3,bind,pure]
  rw [Lean.Loop.forIn_eq_of_monadTail]
  simp only [stop,bind,pure]

private theorem record_v :
    (⟨.ReservedFrz false,false,.Read⟩ : LocationState).recordNewAccess .Write .ForeignAccess =
      .Recorded ⟨.ReservedFrz false,false,.Write⟩ := rfl
private theorem perform_v :
    (⟨.ReservedFrz false,false,.Write⟩ : LocationState).performAccess .Write .ForeignAccess false =
      .Success ⟨.Disabled,false,.Write⟩ ⟨.ReservedFrz false,.Disabled⟩ := rfl

/-- The revised postorder rule completes this corrected-access component. -/
theorem actual_completed :
    (correctedTree.performWildcardAccessAt correctedLocation (ix 1) (some (tag 4)) .Write {} true).status =
      .Completed := by cbv

theorem child_effects_retained :
    (correctedTree.performWildcardAccessAt correctedLocation (ix 1) (some (tag 4)) .Write {} true).location.perms.get (ix 4) =
      some ⟨.Disabled,false,.Write⟩ := by cbv


theorem child_cache_retained :
    (correctedTree.performWildcardAccessAt correctedLocation (ix 1) (some (tag 4)) .Write {} true).location.exposedCache = afterCache := by cbv


end DuplicatePrefix.CandidateWriteSupportCorrectedAccess

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateWriteSupportCorrectedAccess." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved corrected component dependency {dependency}"
