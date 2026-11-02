import duplicate_prefix.GeneralBorrowSharedRootBankGeneration
import duplicate_prefix.GeneralBorrowForestFunctionSafety

namespace DuplicatePrefix.GeneralBorrowSharedRootBankFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree
open DuplicatePrefix.ActualReferenceContext DuplicatePrefix.GeneralBorrowSharedRootBankGeneration
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Real allocation, an arbitrary finite prior-parent branching shared
history on a positive requested subslice, then EVERY UInt64 count's genuine
ROOT invocation from the ORIGINAL mutable root through physical return and
NoUB. Root ownership and entry Data are internally restored; the final shared
child is never treated as mutable. No graph/ownership/allocator/Data, completed
operation or trace is a final input premise. -/
theorem invoke (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (steps : List (BorTag × Nat)) (choices : GeneralBorrowSharedRootBankHistory.Choices 1 steps)
    (unique : (steps.map Prod.fst).Nodup) (rootUnused : rootTag ∉ steps.map Prod.fst) (tagUnused : tag ∉ steps.map Prod.fst)
    (reserve : Fin 5 → BorTag) (reserved : ∀ i, reserve i ∉ rootTag :: steps.map Prod.fst)
    (room : 1+steps.length+4 ≤ 4294967295)
    (s : GeneralBorrowForestCaller.Caller
      (generate capacity nonzero rootTag tag different offset len positive bounds steps choices unique rootUnused tagUnused reserve reserved room).state.bank.tree
      rootTag tag offset len reserve) (count : UInt64) :
    GeneralBorrowSharedRootBankHistory.Run positive
      (initial capacity nonzero rootTag tag different offset len bounds) steps
      (generate capacity nonzero rootTag tag different offset len positive bounds steps choices unique rootUnused tagUnused reserve reserved room).state ∧
    (generate capacity nonzero rootTag tag different offset len positive bounds steps choices unique rootUnused tagUnused reserve reserved room).state.bank.handles.length = 1+steps.length ∧
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
  refine ⟨generated.history,generated.length,?_⟩
  exact GeneralBorrowForestFunctionSafety.invoke generated.state.bank.tree GeneralBorrowFullSharedSeed.root generated.state.bank.resources
    rootTag tag offset len (GeneralBorrowSharedRootBankState.entryData generated.state tag generated.fresh)
    reserve generated.reserved s count
end
end DuplicatePrefix.GeneralBorrowSharedRootBankFunctionSafety
