import duplicate_prefix.GeneralBorrowRawRootAcceptedObserved
import duplicate_prefix.GeneralBorrowRawRootRejectedObserved
import duplicate_prefix.GeneralBorrowRawRootZeroDescribed
import duplicate_prefix.GeneralBorrowRawRootAllCount
namespace DuplicatePrefix.GeneralBorrowRawRootObservedAllCount
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext GenericFunctionEntryState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
abbrev Initial := GeneralBorrowRawRootZeroEntry.Initial
/-- ONE original call and ONE actual terminal heap, with the observed return
slot bytes attached to that SAME terminal state. All finite permitted prefixes
are free of errors and UB. This result does not classify admissible callers. -/
structure Outcome (s : Initial) (n : UInt64) where
  entry : CompilerFrameContext.ActualFrame
  initial : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  final : MachineHooks.State MiriMemoryKind Machine.RootUser
  call : GeneralBorrowRawRootPositivePrefix.ActualCall s n entry initial
  trace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits (Storage.withCurrent #[] entry initial) final
  terminal : ExecutionMachine.step (config s.options (s.remaining+1) s.span) s.limits () final = (final,.ok false)
  empty : final.stack.frames = #[]
  noErrors : CallSafety.NoErrorsBeforeReturn ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ 1 (Storage.withCurrent #[] entry initial)
  safe : CallSafety.NoUBBeforeReturn ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ 1 (Storage.withCurrent #[] entry initial)
  progress : ∀ reachable,SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits (Storage.withCurrent #[] entry initial) reachable →
    ∃ next continuing,ExecutionMachine.step (config s.options (s.remaining+1) s.span) s.limits () reachable = (next,.ok continuing)
  context : PhysicalMachineWrite.Context
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotPresent : final.machine.memory.live.find? (fun row => row.1 == s.slotId) = some (s.slotId,slot)
  encoded : GeneralBorrowRawReturnedBytes.Encoded context slot.allocation (GeneralBorrowRawRootAllCount.expected s.len n)

theorem Outcome.safety {s : Initial} {n : UInt64} (outcome : Outcome s n) :
    DuplicatePrefixArgumentCallResult.Result s.options s.limits s.remaining s.span s.before
      (.pointer (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset)))) s.len n s.place := by
  apply (DuplicatePrefixArgumentCallResult.pointer_iff _ _ _ _ _ _ _ _ _).mpr
  exact ⟨Storage.withCurrent #[] outcome.entry outcome.initial,outcome.final,outcome.call,outcome.trace,outcome.terminal,
    outcome.empty,outcome.noErrors,outcome.safe,outcome.progress⟩

/-- All counts, including zero and rejected counts, use the SAME original
count-independent contract. The one-byte physical return is true exactly when
count=0 or count≤len/2. Concrete positive-slice, conditional order, fixed
metadata/configuration and resource scope remain explicit; this is not a
claim that every otherwise-valid Rust input/state satisfies these premises. -/
theorem invoke (s : Initial)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+5 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+5 < 18446744073709551615)
    (bytes : GeneralBorrowRawSliceBytes.Data s.entry.allocation s.offset s.len)
    (bufferExtras : s.before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == s.id) = some (s.id,⟨none,#[]⟩))
    (statementFuel : s.limits.validation = s.validityFuel+1) (n : UInt64) : Nonempty (Outcome s n) := by
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit := ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩
  by_cases zero : n = 0
  · subst n
    obtain ⟨input,options,limits,remaining,span,slotId,context,call,result⟩ := GeneralBorrowRawRootZeroDescribed.invoke s
    obtain ⟨updated,trace,terminal,safe,rest⟩ := result
    let final := CanonicalCopy.replaceAllocation (GeneralBorrowRawRootZeroPhysical.popped input) input.release.slotId input.release.slot.kind updated
    have trace' : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits (Storage.withCurrent #[] input.before input.machine) final := by
      simpa only [GeneralBorrowRawRootZeroPhysical.caller,options,limits,remaining,span] using trace
    have terminal' : ExecutionMachine.step (config s.options (s.remaining+1) s.span) s.limits () final = (final,.ok false) := by
      simpa only [options,limits,remaining,span] using terminal
    have entry : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] input.before input.machine) := ⟨by decide,rfl⟩
    have past : CallSafety.pastCallBoundary 1 final := by change 0<1;decide
    have encoded : GeneralBorrowRawReturnedBytes.Encoded input.context updated true := {
      size:=rest.2.1.trans input.slotSize,storage:=rest.2.2.1.trans input.slotStorage,
      mask:=by rw [rest.2.2.2.1,input.slotSize],provenance:=rest.2.2.2.2.1,
      mutable:=rest.2.2.2.2.2.2.trans input.slotMutable,width:=input.runtimeWidth,
      bytes:=by simpa only [input.slotSize,ite_true] using rest.2.2.2.2.2.1 }
    refine ⟨{
      entry:=input.before,initial:=input.machine,final:=final,call:=call,trace:=trace',terminal:=terminal',empty:=rfl,
      noErrors:=SuccessfulTrace.no_errors safety 1 _ _ entry trace' past,safe:=?_,
      progress:=SuccessfulTraceTerminal.prefix_step_success trace' terminal',context:=input.context,
      slot:=⟨input.release.slot.kind,updated⟩,slotPresent:=?_,encoded:=?_}⟩
    · simpa only [GeneralBorrowRawRootZeroPhysical.caller,options,limits,remaining,span] using safe
    · change (CanonicalCopy.replaceAllocation _ _ _ _).machine.memory.live.find? _ = _
      rw [←slotId]
      exact CanonicalCopy.replace_lookup _ _ _ _
    · simpa [GeneralBorrowRawRootAllCount.expected] using encoded
  by_cases within : n ≤ s.len/2
  · obtain ⟨entryFrame,initial,physical,call,value,slotId,result,updated,trace,terminal,safe,encoded⟩ :=
      GeneralBorrowRawRootAcceptedObserved.invoke s n zero within preciseOff implicitOff budget dispatch nodeMargin tagMargin bytes bufferExtras statementFuel
    let final := CanonicalCopy.replaceAllocation (GeneralBorrowRawRootBoolReturn.popped physical) physical.release.slotId physical.release.slot.kind updated
    have entry : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] entryFrame initial) := ⟨by decide,rfl⟩
    have past : CallSafety.pastCallBoundary 1 final := by change 0<1;decide
    refine ⟨{
      entry:=entryFrame,initial:=initial,final:=final,call:=call,trace:=trace,terminal:=terminal,empty:=rfl,
      noErrors:=SuccessfulTrace.no_errors safety 1 _ _ entry trace past,safe:=safe,
      progress:=SuccessfulTraceTerminal.prefix_step_success trace terminal,context:=physical.context,
      slot:=⟨physical.release.slot.kind,updated⟩,slotPresent:=?_,encoded:=?_}⟩
    · change (CanonicalCopy.replaceAllocation _ _ _ _).machine.memory.live.find? _ = _
      rw [←slotId]
      exact CanonicalCopy.replace_lookup _ _ _ _
    · simpa [GeneralBorrowRawRootAllCount.expected,within] using encoded
  · have rejected : n > s.len/2 := UInt64.not_le.mp within
    obtain ⟨prepared,result,updated,trace,noErrors,safe,terminal,value,empty,encoded⟩ :=
      GeneralBorrowRawRootRejectedObserved.invoke s n zero rejected preciseOff implicitOff budget dispatch (by omega) (by omega)
    let final := CanonicalCopy.replaceAllocation (GeneralBorrowRawRootBoolReturn.popped result.physical) result.physical.release.slotId result.physical.release.slot.kind updated
    refine ⟨{
      entry:=prepared.entry,initial:=prepared.initial,final:=final,call:=prepared.call,trace:=trace,terminal:=terminal,empty:=empty,
      noErrors:=noErrors,safe:=safe,progress:=SuccessfulTraceTerminal.prefix_step_success trace terminal,context:=result.physical.context,
      slot:=⟨result.physical.release.slot.kind,updated⟩,slotPresent:=?_,encoded:=?_}⟩
    · change (CanonicalCopy.replaceAllocation _ _ _ _).machine.memory.live.find? _ = _
      have slotId := result.slotId.trans prepared.slotId
      rw [←slotId]
      exact CanonicalCopy.replace_lookup _ _ _ _
    · simpa [GeneralBorrowRawRootAllCount.expected,zero,within] using encoded
end
end DuplicatePrefix.GeneralBorrowRawRootObservedAllCount
