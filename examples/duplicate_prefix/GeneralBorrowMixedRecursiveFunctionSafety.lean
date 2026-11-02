import duplicate_prefix.GeneralBorrowMixedRecursiveGeneration
import duplicate_prefix.GeneralBorrowForestFunctionSafety

namespace DuplicatePrefix.GeneralBorrowMixedRecursiveFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree
open DuplicatePrefix.ActualReferenceContext DuplicatePrefix.GeneralBorrowMixedRecursiveGeneration
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Actual mixed root Read/Write/shared/default/activation/zero/GC formation,
then an arbitrary-depth unprotected descendant chain on a positive subslice,
then every count's genuine invocation through physical return and NoUB from
the ORIGINAL root. All history completions, graph/ownership/allocator and entry
Data are internally derived. The final readonly descendant is not made mutable. -/
theorem invoke (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (prior : List (GeneralBorrowPartitionGcHistory.Action capacity))
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (tags : List BorTag)
    (unique : ((prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags) ++ tags).Nodup)
    (rootUnused : rootTag ∉ (prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags) ++ tags)
    (tagUnused : tag ∉ (prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags) ++ tags)
    (reserve : Fin 5 → BorTag)
    (reserved : ∀ i, reserve i ∉ rootTag :: ((prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags) ++ tags))
    (room : 1+((prior.flatMap GeneralBorrowPartitionGcHistory.Action.tags) ++ tags).length+4 ≤ 4294967295)
    (s : GeneralBorrowForestCaller.Caller
      (generate capacity nonzero rootTag tag different prior offset len positive bounds tags unique rootUnused tagUnused reserve reserved room).state.tree
      rootTag tag offset len reserve) (count : UInt64) :
    let built := generate capacity nonzero rootTag tag different prior offset len positive bounds tags unique rootUnused tagUnused reserve reserved room
    GeneralBorrowPartitionGcHistory.AllCompleted (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity prior ∧
    GeneralBorrowRecursiveSharedHistory.Run positive
      (GeneralBorrowRecursiveSharedGeneration.of_partition _ GeneralBorrowFullSharedSeed.root capacity built.prefixState offset len bounds)
      (GeneralBorrowRecursiveCallGeneration.actions tags) built.state ∧
    GeneralBorrowRecursiveSharedHistory.height built.state = tags.length+1 ∧
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
  let built := generate capacity nonzero rootTag tag different prior offset len positive bounds tags unique rootUnused tagUnused reserve reserved room
  refine ⟨built.prefixCompleted,built.history,built.height,?_⟩
  exact GeneralBorrowForestFunctionSafety.invoke built.state.tree GeneralBorrowFullSharedSeed.root built.state.resources
    rootTag tag offset len (GeneralBorrowRecursiveRootRestore.entryData built.state rootTag tag built.facts built.fresh)
    reserve built.reserved s count
end
end DuplicatePrefix.GeneralBorrowMixedRecursiveFunctionSafety
