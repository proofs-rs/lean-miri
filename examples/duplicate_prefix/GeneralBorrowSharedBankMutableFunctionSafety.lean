import duplicate_prefix.GeneralBorrowSharedBankMutableGeneration
import duplicate_prefix.GeneralBorrowForestFunctionSafety

namespace DuplicatePrefix.GeneralBorrowSharedBankMutableFunctionSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open Miri.DataStructures Miri.TreeBorrows.Tree
open DuplicatePrefix.ActualReferenceContext DuplicatePrefix.GeneralBorrowSharedBankMutableGeneration
open DuplicatePrefix.GeneralBorrowSharedBankMutableAction
open DuplicatePrefix.GeneralBorrowSharedRootBankGeneration (initial)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- Actual allocation and any finite interleaving of arbitrary prior-parent
shared branching constructors, original-root exposures, root Read/Write, actual unprotected mutable reservations and child Write activations and production full GC precede EVERY UInt64
count's original mutable ROOT invocation through physical return and NoUB.
GC liveness appends the actual current handle tags to arbitrary extra tags.
Every intermediate Read, Write, constructor, exposure and GC success is constructed internally;
no stage graph/ownership/resources/Data or operation success is a premise.
Root Write and mutable episodes discard selectable child handles; root Read retains them. The episode child remains in its actual output tree; later GC may remove unreachable nodes.
Static parent-position choices follow this reset. Scope is positive requested
subslices with empty global protections. -/
theorem invoke (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag tag : BorTag) (different : rootTag ≠ tag)
    (offset len : UInt64) (positive : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (actions : List Action) (choices : Choices 1 actions)
    (unique : (tags actions).Nodup) (rootUnused : rootTag ∉ tags actions) (tagUnused : tag ∉ tags actions)
    (reserve : Fin 5 → BorTag) (reserved : ∀ i, reserve i ∉ rootTag :: tags actions)
    (room : 1+(tags actions).length+4 ≤ 4294967295)
    (s : GeneralBorrowForestCaller.Caller
      (generate capacity nonzero rootTag tag different offset len positive bounds actions choices unique rootUnused tagUnused reserve reserved room).state.bank.tree
      rootTag tag offset len reserve) (count : UInt64) :
    GeneralBorrowSharedBankMutableHistory.Run positive tag
      (initial capacity nonzero rootTag tag different offset len bounds) actions
      (generate capacity nonzero rootTag tag different offset len positive bounds actions choices unique rootUnused tagUnused reserve reserved room).state ∧
    (generate capacity nonzero rootTag tag different offset len positive bounds actions choices unique rootUnused tagUnused reserve reserved room).state.bank.handles.length = handlesAfter 1 actions ∧
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
  let generated := generate capacity nonzero rootTag tag different offset len positive bounds actions choices unique rootUnused tagUnused reserve reserved room
  refine ⟨generated.history,generated.length,?_⟩
  exact GeneralBorrowForestFunctionSafety.invoke generated.state.bank.tree GeneralBorrowFullSharedSeed.root generated.state.bank.resources
    rootTag tag offset len (GeneralBorrowSharedRootBankState.entryData generated.state tag generated.fresh)
    reserve generated.reserved s count
end
end DuplicatePrefix.GeneralBorrowSharedBankMutableFunctionSafety
