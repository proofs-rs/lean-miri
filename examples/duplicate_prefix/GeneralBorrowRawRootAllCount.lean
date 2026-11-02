import duplicate_prefix.GeneralBorrowRawRootAcceptedInvoke
import duplicate_prefix.GeneralBorrowRawRootRejectedCompleteCall
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.SuccessfulTraceTerminal
namespace DuplicatePrefix.GeneralBorrowRawRootAllCount
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial

def expected (len count : UInt64) : Bool := decide (count = 0 ∨ count ≤ len/2)

/-- Shape-free actual call result for every UInt64 count under the SAME
count-independent initial contract. Concrete pointer/positive-slice/conditional
parent order/configuration/external metadata/resource restrictions remain in
Initial and the explicit added hypotheses; no all-valid-input coverage claim
is made by this theorem. Every branch executes the actual physical Bool return. -/
theorem invoke (s : Initial)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+5 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+5 < 18446744073709551615)
    (bytes : GeneralBorrowRawSliceBytes.Data s.entry.allocation s.offset s.len)
    (bufferExtras : s.before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == s.id) = some (s.id,⟨none,#[]⟩))
    (statementFuel : s.limits.validation = s.validityFuel+1) (n : UInt64) :
    DuplicatePrefixArgumentCallResult.Result s.options s.limits s.remaining s.span s.before
      (.pointer (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset)))) s.len n s.place := by
  apply (DuplicatePrefixArgumentCallResult.pointer_iff _ _ _ _ _ _ _ _ _).mpr
  let cfg := config s.options (s.remaining+1) s.span
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨cfg,s.limits,fun _ _ => True⟩
  by_cases zero : n = 0
  · subst n
    obtain ⟨input,options,limits,remaining,span,call,result⟩ := GeneralBorrowRawRootZeroEntry.invoke s
    obtain ⟨updated,trace,terminal,safe,rest⟩ := result
    let final := CanonicalCopy.replaceAllocation (GeneralBorrowRawRootZeroPhysical.popped input) input.release.slotId input.release.slot.kind updated
    have trace' : SuccessfulTrace.Trace cfg s.limits (Storage.withCurrent #[] input.before input.machine) final := by
      simpa only [GeneralBorrowRawRootZeroPhysical.caller,options,limits,remaining,span] using trace
    have terminal' : ExecutionMachine.step cfg s.limits () final = (final,.ok false) := by
      simpa only [options,limits,remaining,span] using terminal
    have entry : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] input.before input.machine) := ⟨by decide,rfl⟩
    have past : CallSafety.pastCallBoundary 1 final := by change 0<1;decide
    refine ⟨Storage.withCurrent #[] input.before input.machine,final,call,trace',terminal',rfl,
      SuccessfulTrace.no_errors safety 1 _ _ entry trace' past,?_,SuccessfulTraceTerminal.prefix_step_success trace' terminal'⟩
    simpa only [GeneralBorrowRawRootZeroPhysical.caller,options,limits,remaining,span] using safe
  by_cases within : n ≤ s.len/2
  · obtain ⟨entryFrame,initial,physical,call,value,slotId,result,updated,trace,terminal,safe⟩ :=
      GeneralBorrowRawRootAcceptedInvoke.invoke s n zero within preciseOff implicitOff budget dispatch nodeMargin tagMargin bytes bufferExtras statementFuel
    let final := CanonicalCopy.replaceAllocation (GeneralBorrowRawRootBoolReturn.popped physical) physical.release.slotId physical.release.slot.kind updated
    have entry : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] entryFrame initial) := ⟨by decide,rfl⟩
    have past : CallSafety.pastCallBoundary 1 final := by change 0<1;decide
    exact ⟨Storage.withCurrent #[] entryFrame initial,final,call,trace,terminal,rfl,
      SuccessfulTrace.no_errors safety 1 _ _ entry trace past,safe,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
  · have rejected : n > s.len/2 := UInt64.not_le.mp within
    obtain ⟨prepared,result,final,trace,noErrors,safe,terminal,value,empty⟩ :=
      GeneralBorrowRawRootRejectedCompleteCall.invoke s n zero rejected preciseOff implicitOff budget dispatch (by omega) (by omega)
    exact ⟨Storage.withCurrent #[] prepared.entry prepared.initial,final,prepared.call,trace,terminal,empty,
      noErrors,safe,SuccessfulTraceTerminal.prefix_step_success trace terminal⟩
end
end DuplicatePrefix.GeneralBorrowRawRootAllCount
