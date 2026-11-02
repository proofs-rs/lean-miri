import duplicate_prefix.GenericFunctionEntryCommonRejected
import duplicate_prefix.GenericFunctionAcceptedPoolReturn
import duplicate_prefix.GenericFunctionRejectedPoolReturn

namespace DuplicatePrefix.GenericFunctionPoolSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open ActualReferenceContext
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- All UInt64 counts for one positive-length concrete single-root slice.
The common caller contract explicitly supplies arbitrary coherent initial
free-pool/accounting and vacant-slot cleanliness, conservative node capacity,
four future tags, initialized whole-slice storage and fixed runtime/metadata.
Actual selected slots and all intermediate borrow records are constructed.
No branch Input family or operation-success premise is assumed. This does not
classify arbitrary valid Rust borrowing histories or empty references. -/
theorem invoke (s : GenericFunctionEntryCommon.PoolInput) (count : UInt64) :
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
  by_cases zero : count = 0
  · subst count
    obtain ⟨input,optionsEq,limitsEq,remainingEq,spanEq,call,physical⟩ :=
      GenericFunctionEntryZero.invoke (GenericFunctionEntryCommon.pool_to_zero s)
    obtain ⟨updated,trace,terminal,safety,_⟩ := physical
    let installed := Storage.withCurrent #[] input.before input.machine
    let finalState := CanonicalCopy.replaceAllocation (GenericRootZeroPhysical.popped input)
      input.release.slotId input.release.slot.kind updated
    rw [optionsEq,limitsEq,remainingEq,spanEq] at trace terminal safety
    have empty : finalState.stack.frames = #[] := rfl
    exact ⟨installed,finalState,call,trace,terminal,empty,safety,
      SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
  · have positive : (0 : UInt64) < count := UInt64.pos_iff_ne_zero.mpr zero
    by_cases within : count ≤ s.len/2
    · simpa only [GenericFunctionEntryCommon.to_accepted_pool,GenericFunctionEntryCommon.to_accepted_base] using
        GenericFunctionAcceptedPoolReturn.invoke (GenericFunctionEntryCommon.to_accepted_pool s count positive within)
    · have notBound : ¬ count.toNat ≤ (s.len/2).toNat :=
        fun bound => within (UInt64.le_iff_toNat_le.mpr bound)
      have rejected : s.len/2 < count := UInt64.lt_iff_toNat_lt.mpr (by omega)
      simpa only [GenericFunctionEntryCommonRejected.to_rejected_pool,GenericFunctionEntryCommonRejected.to_rejected_base] using
        GenericFunctionRejectedPoolReturn.invoke (GenericFunctionEntryCommonRejected.to_rejected_pool s count positive rejected)

end DuplicatePrefix.GenericFunctionPoolSafety
