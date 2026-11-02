import duplicate_prefix.GeneralBorrowExposedCallGeneration
import duplicate_prefix.GeneralBorrowProtectedSubsliceFunctionSafety
namespace DuplicatePrefix.GeneralBorrowExposedFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree
open DuplicatePrefix.ActualReferenceContext DuplicatePrefix.GeneralBorrowExposedCallGeneration
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
attribute [local irreducible] GeneralBorrowExposedCallGeneration.generate

/-- Actual allocation/shared generation, all-leaf and root exposure, and real
root Write form every count's genuine invocation on any positive interior slice.
The dependent physical Caller uses that exact constructed tree; graph, ownership,
freshness, successful history and cache correctness are derived internally. -/
theorem invoke (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag)
    (different : rootTag ≠ childTag) (tags : List BorTag) (distinct : tags.Nodup)
    (rootUnused : rootTag ∉ tags) (childUnused : childTag ∉ tags)
    (reserve : Fin 5 → BorTag) (reserved : ∀ i,reserve i ∉ rootTag::childTag::tags)
    (short : 2+tags.length < 65536)
    (s : let g := generate capacity nonzero rootTag childTag different tags distinct rootUnused childUnused reserve reserved short;
      GeneralBorrowProtectedSubsliceCaller.Caller (tree g) g.final.parent capacity g.state g.final.newTag reserve)
    (count : UInt64) :
    (let g := generate capacity nonzero rootTag childTag different tags distinct rootUnused childUnused reserve reserved short;
      (GeneralBorrowExposedProtocolWrite.operation g.final g.exposed).status = .Completed) ∧
    let cfg := config s.options (s.remaining+1) s.span
    ∃ installed finalState,
      Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
          (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
          ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second count)] false (.memory s.place) (.stop true)
        ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
      SuccessfulTrace.Trace cfg s.limits installed finalState ∧
      ExecutionMachine.step cfg s.limits () finalState = (finalState,.ok false) ∧
      finalState.stack.frames = #[] ∧
      CallSafety.NoUBBeforeReturn
        (⟨cfg,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
        1 installed ∧
      (∀ before, SuccessfulTrace.Trace cfg s.limits installed before →
        ∃ after continuing, ExecutionMachine.step cfg s.limits () before = (after,.ok continuing)) := by
  let g := generate capacity nonzero rootTag childTag different tags distinct rootUnused childUnused reserve reserved short
  refine ⟨g.completed,?_⟩
  exact GeneralBorrowProtectedSubsliceFunctionSafety.invoke (tree g) g.final.parent capacity g.state
    g.final.newTag g.fresh reserve g.reserved s count
end
end DuplicatePrefix.GeneralBorrowExposedFunctionSafety
