import duplicate_prefix.GeneralBorrowPartialHistoryGeneration
import duplicate_prefix.GeneralBorrowPartitionCaller
import duplicate_prefix.GenericFunctionPoolSafety

namespace DuplicatePrefix.GeneralBorrowPartialHistoryFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree
open DuplicatePrefix.ActualReferenceContext DuplicatePrefix.GeneralBorrowPartialHistoryGeneration
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Actual allocation, mixed full-slice shared/GC history, then arbitrary
interleaved partial-range root Reads/Writes and shared stages yield all counts'
genuine ROOT invocation through physical return and NoUB. No graph, ownership,
allocator, intermediate state, operation success or trace is a final premise. -/
theorem invoke (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) (prior : List GeneralBorrowReusableHistory.Action)
    (actions : List (GeneralBorrowPartitionMixedHistory.Action capacity))
    (unique : ((prior.flatMap GeneralBorrowReusableHistory.Action.tags) ++
      actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags).Nodup)
    (rootUnused : rootTag ∉ (prior.flatMap GeneralBorrowReusableHistory.Action.tags) ++
      actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags)
    (tagUnused : tag ∉ (prior.flatMap GeneralBorrowReusableHistory.Action.tags) ++
      actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags)
    (reserve : Fin 5 → BorTag)
    (reserved : ∀ i, reserve i ∉ rootTag :: ((prior.flatMap GeneralBorrowReusableHistory.Action.tags) ++
      actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags))
    (room : 1+((prior.flatMap GeneralBorrowReusableHistory.Action.tags) ++
      actions.flatMap GeneralBorrowPartitionMixedHistory.Action.tags).length+4 ≤ 4294967295)
    (s : GeneralBorrowPartitionCaller.Caller
      (GeneralBorrowPartitionMixedHistory.execute
        (GeneralBorrowReusableHistory.execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior) rootTag capacity actions)
      GeneralBorrowFullSharedSeed.root capacity
      (generate capacity nonzero rootTag tag different prior actions unique rootUnused tagUnused reserve reserved room).state
      tag reserve) (count : UInt64) :
    GeneralBorrowReusableHistory.AllCompleted (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior ∧
    GeneralBorrowPartitionMixedHistory.AllCompleted
      (GeneralBorrowReusableHistory.execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior) rootTag capacity actions ∧
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
  let generated := generate capacity nonzero rootTag tag different prior actions unique rootUnused tagUnused reserve reserved room
  refine ⟨generated.priorCompleted,generated.completed,?_⟩
  exact GenericFunctionPoolSafety.invoke
    (GeneralBorrowPartitionCaller.pool _ GeneralBorrowFullSharedSeed.root capacity
      generated.state tag generated.fresh reserve generated.reserved s) count
end
end DuplicatePrefix.GeneralBorrowPartialHistoryFunctionSafety
