import duplicate_prefix.GeneralBorrowRecursiveCallGeneration
import duplicate_prefix.GeneralBorrowForestFunctionSafety

namespace DuplicatePrefix.GeneralBorrowRecursiveFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree
open DuplicatePrefix.ActualReferenceContext DuplicatePrefix.GeneralBorrowRecursiveCallGeneration
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Real allocation, an arbitrary finite chain of successive unprotected shared
children on a positive requested subslice, then EVERY UInt64 count's genuine
ROOT invocation from the ORIGINAL mutable root through physical return and
NoUB. Root ownership and entry Data are internally restored; the final shared
child is never treated as mutable. No graph/ownership/allocator/Data, completed
operation or trace is a final input premise. -/
theorem invoke (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (tags : List BorTag) (unique : tags.Nodup) (rootUnused : rootTag ∉ tags) (tagUnused : tag ∉ tags)
    (reserve : Fin 5 → BorTag) (reserved : ∀ i, reserve i ∉ rootTag :: tags)
    (room : 1+tags.length+4 ≤ 4294967295)
    (s : GeneralBorrowForestCaller.Caller
      (generate capacity nonzero rootTag tag different offset len positive bounds tags unique rootUnused tagUnused reserve reserved room).state.tree
      rootTag tag offset len reserve) (count : UInt64) :
    GeneralBorrowRecursiveSharedHistory.Run positive
      (initial capacity nonzero rootTag tag different offset len bounds) (actions tags)
      (generate capacity nonzero rootTag tag different offset len positive bounds tags unique rootUnused tagUnused reserve reserved room).state ∧
    GeneralBorrowRecursiveSharedHistory.height
      (generate capacity nonzero rootTag tag different offset len positive bounds tags unique rootUnused tagUnused reserve reserved room).state = tags.length+1 ∧
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
  let generated := generate capacity nonzero rootTag tag different offset len positive bounds tags unique rootUnused tagUnused reserve reserved room
  refine ⟨generated.history,generated.height,?_⟩
  exact GeneralBorrowForestFunctionSafety.invoke generated.state.tree GeneralBorrowFullSharedSeed.root generated.state.resources
    rootTag tag offset len (GeneralBorrowRecursiveRootRestore.entryData generated.state rootTag tag generated.facts generated.fresh)
    reserve generated.reserved s count
end
end DuplicatePrefix.GeneralBorrowRecursiveFunctionSafety
