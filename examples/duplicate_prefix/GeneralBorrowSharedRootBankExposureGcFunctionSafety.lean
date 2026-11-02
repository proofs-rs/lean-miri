import duplicate_prefix.GeneralBorrowRootExposureGc
import duplicate_prefix.GeneralBorrowForestFunctionSafety

namespace DuplicatePrefix.GeneralBorrowSharedRootBankExposureGcFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree
open DuplicatePrefix.ActualReferenceContext DuplicatePrefix.GeneralBorrowSharedRootBankGeneration
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Real allocation, arbitrary prior-parent shared branching, and actual original-root exposure and one
full production GC precede EVERY UInt64 count's original mutable ROOT call.
Final graph, ownership, allocator, entry Data and operation successes are
constructed internally. Scope has empty global protections and concrete root accesses. -/
theorem invoke (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (steps : List (BorTag × Nat)) (choices : GeneralBorrowSharedRootBankHistory.Choices 1 steps)
    (unique : (steps.map Prod.fst).Nodup) (rootUnused : rootTag ∉ steps.map Prod.fst) (tagUnused : tag ∉ steps.map Prod.fst)
    (reserve : Fin 5 → BorTag) (reserved : ∀ i, reserve i ∉ rootTag :: steps.map Prod.fst)
    (room : 1+steps.length+4 ≤ 4294967295)
    (live : Array BorTag)
    (s : GeneralBorrowForestCaller.Caller
      (GeneralBorrowGcRootResources.after ((generate capacity nonzero rootTag tag different offset len positive bounds steps choices unique rootUnused tagUnused reserve reserved room).state.bank.tree.exposeTag {} rootTag).tree live)
      rootTag tag offset len reserve) (count : UInt64) :
    GeneralBorrowSharedRootBankHistory.Run positive
      (initial capacity nonzero rootTag tag different offset len bounds) steps
      (generate capacity nonzero rootTag tag different offset len positive bounds steps choices unique rootUnused tagUnused reserve reserved room).state ∧
    (generate capacity nonzero rootTag tag different offset len positive bounds steps choices unique rootUnused tagUnused reserve reserved room).state.bank.handles.length = 1+steps.length ∧
    ((generate capacity nonzero rootTag tag different offset len positive bounds steps choices unique rootUnused tagUnused reserve reserved room).state.bank.tree.exposeTag {} rootTag).outcome = .ok () ∧
    (((generate capacity nonzero rootTag tag different offset len positive bounds steps choices unique rootUnused tagUnused reserve reserved room).state.bank.tree.exposeTag {} rootTag).tree.removeUnreachableTags live).outcome = .ok () ∧
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
  let generated := generate capacity nonzero rootTag tag different offset len positive bounds steps choices unique rootUnused tagUnused reserve reserved room
  let collected := GeneralBorrowRootExposureGc.collect generated.state positive tag generated.fresh reserve generated.reserved live
  refine ⟨generated.history,generated.length,GeneralBorrowRootExposureGc.expose generated.state,collected.completed,?_⟩
  exact GeneralBorrowForestFunctionSafety.invoke _ GeneralBorrowFullSharedSeed.root collected.resources
    rootTag tag offset len (GeneralBorrowGcRootResources.entryData collected) reserve collected.reserved s count
end
end DuplicatePrefix.GeneralBorrowSharedRootBankExposureGcFunctionSafety
