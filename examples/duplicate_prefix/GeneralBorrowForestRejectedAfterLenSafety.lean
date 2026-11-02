import duplicate_prefix.GeneralBorrowForestRejectedAfterLen
namespace DuplicatePrefix.GeneralBorrowForestRejectedAfterLenSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open ActualReferenceContext
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- From the physical shared-expression boundary, the positive rejected case
executes shared FnEntry validation/copy, the len helper, its actual lifetime,
the guard and false assignment, both root releases and physical bool return.
All permitted reachable finite prefixes of this fixed Unit-choice ROOT suffix
are UB-free. Initial caller/configuration/resource data remain explicit. -/
theorem invoke (s : GeneralBorrowForestRejectedAfterLen.Initial) :
    let cfg := config s.options (s.remaining+1) s.span
    let initial := Storage.withCurrent #[] s.caller s.beforeMachine
    let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
      ⟨cfg,s.limits,fun _ _ => True⟩
    ∃ (input : GeneralBorrowForestRootRejectedPhysical.Input) (updated : Allocation Provenance BorrowTree),
      input.options=s.options ∧ input.limits=s.limits ∧ input.remaining=s.remaining ∧ input.span=s.span ∧
      let done := CanonicalCopy.replaceAllocation (GeneralBorrowForestRootRejectedPhysical.popped input)
        input.release.slotId input.release.slot.kind updated
      SuccessfulTrace.Trace cfg s.limits initial done ∧
      ExecutionMachine.step cfg s.limits () done = (done,.ok false) ∧
      CallSafety.NoUBBeforeReturn safety 1 initial ∧
      target_bytes input.context.access.runtime.base input.release.slot.allocation.byteSize 0 = .ok (AllocationCopy.snapshot updated) := by
  obtain ⟨input,options,limits,remaining,span,prefixTrace,result⟩ := GeneralBorrowForestRejectedAfterLen.complete s
  obtain ⟨updated,suffixTrace,terminal,_,tree,size,len,mask,provenance,bytes,mutability⟩ := result
  have suffix := suffixTrace
  simp only [options,limits,remaining,span] at suffix
  have trace := SuccessfulTrace.append prefixTrace suffix
  have terminal' := terminal
  simp only [options,limits,remaining,span] at terminal'
  let done := CanonicalCopy.replaceAllocation (GeneralBorrowForestRootRejectedPhysical.popped input)
    input.release.slotId input.release.slot.kind updated
  let cfg := config s.options (s.remaining+1) s.span
  let initial := Storage.withCurrent #[] s.caller s.beforeMachine
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨cfg,s.limits,fun _ _ => True⟩
  have entry : CallSafety.IsCallEntry 1 initial := ⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 done := by
    change 0 < 1
    decide
  have safe := SuccessfulTrace.no_ub safety 1 initial done entry trace past
  exact ⟨input,updated,options,limits,remaining,span,trace,terminal',safe,bytes⟩
end
end DuplicatePrefix.GeneralBorrowForestRejectedAfterLenSafety
