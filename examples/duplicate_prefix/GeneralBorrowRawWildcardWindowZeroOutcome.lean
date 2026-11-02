import duplicate_prefix.GeneralBorrowRawWildcardWindowZero
import duplicate_prefix.GeneralBorrowRawReturnedBytes
import duplicate_prefix.DuplicatePrefixArgumentCallResult
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowZeroOutcome
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowRawWildcardWindowInitial
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
/-- One genuine original wildcard call and one terminal state, whose original
return slot contains initialized TRUE. Every permitted finite prefix is safe. -/
structure Outcome (s : Initial) where
  entry : CompilerFrameContext.ActualFrame
  initial : MachineHooks.MachineState MiriMemoryKind Machine.RootUser
  final : MachineHooks.State MiriMemoryKind Machine.RootUser
  call : ActualCall s 0 entry initial
  trace : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits (Storage.withCurrent #[] entry initial) final
  terminal : ExecutionMachine.step (config s.options (s.remaining+1) s.span) s.limits () final = (final,.ok false)
  empty : final.stack.frames = #[]
  noErrors : CallSafety.NoErrorsBeforeReturn ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ 1 (Storage.withCurrent #[] entry initial)
  safe : CallSafety.NoUBBeforeReturn ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩ 1 (Storage.withCurrent #[] entry initial)
  progress : ∀ reachable,SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits (Storage.withCurrent #[] entry initial) reachable →
    ∃ next continuing,ExecutionMachine.step (config s.options (s.remaining+1) s.span) s.limits () reachable = (next,.ok continuing)
  slot : LocalAllocation Provenance BorrowTree MiriMemoryKind
  slotPresent : final.machine.memory.live.find? (fun row => row.1 == s.slotId) = some (s.slotId,slot)
  encoded : GeneralBorrowRawReturnedBytes.Encoded s.writeContext slot.allocation true

theorem Outcome.safety {s : Initial} (outcome : Outcome s) :
    DuplicatePrefixArgumentCallResult.Result s.options s.limits s.remaining s.span s.before
      (.pointer (Pointer.new .wildcard (Size.ofBytes s.address))) s.len 0 s.place := by
  apply (DuplicatePrefixArgumentCallResult.pointer_iff _ _ _ _ _ _ _ _ _).mpr
  exact ⟨Storage.withCurrent #[] outcome.entry outcome.initial,outcome.final,outcome.call,outcome.trace,outcome.terminal,
    outcome.empty,outcome.noErrors,outcome.safe,outcome.progress⟩

theorem invoke (s : Initial) : Nonempty (Outcome s) := by
  obtain ⟨input,options,limits,remaining,span,slotId,context,call,result⟩ := GeneralBorrowRawWildcardWindowZero.invoke s
  obtain ⟨updated,trace,terminal,safe,rest⟩ := result
  let final := CanonicalCopy.replaceAllocation (GeneralBorrowFreshRootScopedRootZeroPhysical.popped input) input.release.slotId input.release.slot.kind updated
  have trace' : SuccessfulTrace.Trace (config s.options (s.remaining+1) s.span) s.limits (Storage.withCurrent #[] input.before input.machine) final := by
    simpa only [GeneralBorrowFreshRootScopedRootZeroPhysical.caller,options,limits,remaining,span] using trace
  have terminal' : ExecutionMachine.step (config s.options (s.remaining+1) s.span) s.limits () final = (final,.ok false) := by
    simpa only [options,limits,remaining,span] using terminal
  have entry : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] input.before input.machine) := ⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final := by change 0<1;decide
  have encoded : GeneralBorrowRawReturnedBytes.Encoded input.context updated true := {
    size:=rest.2.1.trans input.slotSize,storage:=rest.2.2.1.trans input.slotStorage,
    mask:=by rw [rest.2.2.2.1,input.slotSize],provenance:=rest.2.2.2.2.1,
    mutable:=rest.2.2.2.2.2.2.trans input.slotMutable,width:=input.runtimeWidth,
    bytes:=by simpa only [input.slotSize,ite_true] using rest.2.2.2.2.2.1 }
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨config s.options (s.remaining+1) s.span,s.limits,fun _ _ => True⟩
  refine ⟨{
    entry:=input.before,initial:=input.machine,final:=final,call:=call,trace:=trace',terminal:=terminal',empty:=rfl,
    noErrors:=SuccessfulTrace.no_errors safety 1 _ _ entry trace' past,safe:=?_,
    progress:=SuccessfulTraceTerminal.prefix_step_success trace' terminal',
    slot:=⟨input.release.slot.kind,updated⟩,slotPresent:=?_,encoded:=?_}⟩
  · simpa only [GeneralBorrowFreshRootScopedRootZeroPhysical.caller,options,limits,remaining,span] using safe
  · change (CanonicalCopy.replaceAllocation _ _ _ _).machine.memory.live.find? _ = _
    rw [←slotId]
    exact CanonicalCopy.replace_lookup _ _ _ _
  · simpa only [context] using encoded
end
end DuplicatePrefix.GeneralBorrowRawWildcardWindowZeroOutcome
