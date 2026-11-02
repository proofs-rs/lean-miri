import duplicate_prefix.GeneralBorrowForestAllCountInput
namespace DuplicatePrefix.GeneralBorrowForestAllCountSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open ActualReferenceContext
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def Result (s : GeneralBorrowForestAllCountInput.Initial) : Prop :=
  let cfg := config s.options (s.remaining+1) s.span
  ∃ installed finalState,
    Call.initStackFrame (ExecutionMachine.callHooks cfg s.limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (RetagReferencePlace.sliceValue (config s.options s.remaining s.span).access.runtime.base
        (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len ActualReferenceMetadata.reference).imm,
        ActualReferenceMetadata.reference⟩,.Copy (EmptyRootArguments.second s.count)] false (.memory s.place) (.stop true)
      ⟨⟨#[]⟩,s.before⟩ = .ok () installed ∧
    SuccessfulTrace.Trace cfg s.limits installed finalState ∧
    ExecutionMachine.step cfg s.limits () finalState = (finalState,.ok false) ∧
    finalState.stack.frames = #[] ∧
    CallSafety.NoUBBeforeReturn
      (⟨cfg,s.limits,fun _ _ => True⟩ : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit)
      1 installed ∧
    (∀ before, SuccessfulTrace.Trace cfg s.limits installed before →
      ∃ after continuing, ExecutionMachine.step cfg s.limits () before = (after,.ok continuing))

/-- Arbitrary count on a positive-length multiple-root slice, from one original
caller/resource contract. The three branches invoke real original-call proofs:
zero returns true; accepted positive count performs the actual physical copy
and true return; rejected count performs the physical false return. Every
permitted reachable finite Unit-choice prefix succeeds. This does not classify
arbitrary Rust histories or the separate zero-length slice case. -/
theorem invoke (s : GeneralBorrowForestAllCountInput.Initial) : Result s := by
  by_cases zero : s.count = 0
  · simpa only [Result,zero] using GeneralBorrowForestZeroSafety.invoke s.toOriginal
  · have positive : (0 : UInt64) < s.count := UInt64.pos_iff_ne_zero.mpr zero
    by_cases within : s.count ≤ s.len/2
    · let input := GeneralBorrowForestAllCountInput.accepted s positive within
      obtain ⟨slot,ready,finalState,call,physical,trace,terminal,empty,safe,all⟩ := GeneralBorrowForestAcceptedFunctionSafety.invoke input
      let installed := Storage.withCurrent #[] (GeneralBorrowForestNonzeroMachinePrefix.entryFrame input.toPrefix)
        (GeneralBorrowForestNonzeroMachinePrefix.entryMachine input.toPrefix slot)
      exact ⟨installed,finalState,call,trace,terminal,empty,safe,all⟩
    · have outside : s.count > s.len/2 := UInt64.lt_iff_toNat_lt.mpr
        (Nat.lt_of_not_ge (fun bound => within (UInt64.le_iff_toNat_le.mpr bound)))
      let input := GeneralBorrowForestAllCountInput.rejected s outside
      obtain ⟨slot,physical,returned,call,trace,terminal,safe,bytes⟩ := GeneralBorrowForestRejectedFunctionSafety.invoke input
      let installed := Storage.withCurrent #[] (GeneralBorrowForestRejectedMachineAssembly.entryFrame input.toMachine)
        (GeneralBorrowForestRejectedMachineAssembly.entryMachine input.toMachine slot)
      let finalState := CanonicalCopy.replaceAllocation (GeneralBorrowForestRootRejectedPhysical.popped physical)
        physical.release.slotId physical.release.slot.kind returned
      exact ⟨installed,finalState,call,trace,terminal,rfl,safe,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.GeneralBorrowForestAllCountSafety
