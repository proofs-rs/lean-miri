import duplicate_prefix.GeneralBorrowPartitionGcGeneration
import duplicate_prefix.GeneralBorrowSubsliceFunctionSafety
import duplicate_prefix.GeneralBorrowProtectedSubsliceFunctionSafety

namespace DuplicatePrefix.GeneralBorrowPartitionGcFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree
open DuplicatePrefix.ActualReferenceContext DuplicatePrefix.GeneralBorrowPartitionGcHistory DuplicatePrefix.GeneralBorrowPartitionGcGeneration
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Actual allocation and arbitrary partial-range root access/shared/default/GC
interleavings (including zero constructors and reserved-child Write activation) form every count's genuine invocation for any positive in-bounds
allocation-interior input slice. Nonempty global protectors disjoint from the
target tree are permitted under the explicit physical protector contract.
Graph, ownership, successful operations and
traces are conclusions; resource and physical caller contracts are explicit. -/
theorem invoke (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag)
    (different : rootTag ≠ tag) (actions : List (Action capacity))
    (unique : (actions.flatMap Action.tags).Nodup) (rootUnused : rootTag ∉ actions.flatMap Action.tags)
    (tagUnused : tag ∉ actions.flatMap Action.tags) (reserve : Fin 5 → BorTag)
    (reserved : ∀ i, reserve i ∉ rootTag :: actions.flatMap Action.tags)
    (room : 1+(actions.flatMap Action.tags).length+4 ≤ 4294967295)
    (s : GeneralBorrowProtectedSubsliceCaller.Caller
      (execute (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions)
      GeneralBorrowFullSharedSeed.root capacity
      (generate capacity nonzero rootTag tag different actions unique rootUnused tagUnused reserve reserved room).state tag reserve)
    (count : UInt64) :
    AllCompleted (BorrowTree.new rootTag (Size.ofBytes capacity)) rootTag capacity actions ∧
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
  let generated := generate capacity nonzero rootTag tag different actions unique rootUnused tagUnused reserve reserved room
  refine ⟨generated.completed,?_⟩
  exact GeneralBorrowProtectedSubsliceFunctionSafety.invoke _ GeneralBorrowFullSharedSeed.root capacity generated.state
    tag generated.fresh reserve generated.reserved s count
end
end DuplicatePrefix.GeneralBorrowPartitionGcFunctionSafety
