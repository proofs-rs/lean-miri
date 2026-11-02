import duplicate_prefix.GeneralBorrowPartitionGeneration
import duplicate_prefix.GeneralBorrowPartitionCaller
import duplicate_prefix.GenericFunctionPoolSafety

namespace DuplicatePrefix.GeneralBorrowPartitionFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree
open DuplicatePrefix.ActualReferenceContext DuplicatePrefix.GeneralBorrowReusableHistory
open DuplicatePrefix.GeneralBorrowReusableGeneration
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Allocation-derived shared/GC/reuse history followed by any finite sequence
of in-bounds partial-range root Reads/Writes yields every count's genuine ROOT
invocation through physical return and NoUB. Bounds, resources and the physical
caller contract are explicit; graph, ownership, completed operations and traces
are all derived. Partial-range shared/mutable constructors are not included. -/
theorem invoke (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) (actions : List Action)
    (unique : (actions.flatMap Action.tags).Nodup)
    (rootUnused : rootTag ∉ actions.flatMap Action.tags)
    (tagUnused : tag ∉ actions.flatMap Action.tags)
    (reserve : Fin 5 → BorTag)
    (reserved : ∀ i, reserve i ∉ rootTag :: actions.flatMap Action.tags)
    (room : 1+(actions.flatMap Action.tags).length+4 ≤ 4294967295)
    (accesses : List (GeneralBorrowPartitionHistory.Action capacity))
    (s : GeneralBorrowPartitionCaller.Caller
      (GeneralBorrowPartitionHistory.execute (execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions) rootTag accesses)
      GeneralBorrowFullSharedSeed.root capacity
      (GeneralBorrowPartitionGeneration.extend capacity rootTag tag actions reserve
        (generate capacity nonzero rootTag tag different actions unique rootUnused tagUnused reserve reserved room) accesses).state
      tag reserve) (count : UInt64) :
    AllCompleted (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions ∧
    GeneralBorrowPartitionHistory.AllCompleted (execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions) rootTag accesses ∧
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
  let initial := generate capacity nonzero rootTag tag different actions unique rootUnused tagUnused reserve reserved room
  let generated := GeneralBorrowPartitionGeneration.extend capacity rootTag tag actions reserve initial accesses
  refine ⟨generated.prefixCompleted,generated.suffixCompleted,?_⟩
  exact GenericFunctionPoolSafety.invoke
    (GeneralBorrowPartitionCaller.pool _ GeneralBorrowFullSharedSeed.root capacity
      generated.state tag generated.fresh reserve generated.reserved s) count
end
end DuplicatePrefix.GeneralBorrowPartitionFunctionSafety
