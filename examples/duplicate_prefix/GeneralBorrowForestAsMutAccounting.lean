import duplicate_prefix.GeneralBorrowForestAsMutInvocation
namespace DuplicatePrefix.GeneralBorrowForestAsMutAccounting
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
/- Source terminator accounting transports the pre-call contract. -/
noncomputable section

def core (s : GeneralBorrowForestAsMutInvocationCore.Input) : GeneralBorrowForestAsMutInvocationCore.Input := by
  let next := AsMutPtrReturn.accountedMachine s.options s.remaining s.span s.machine
  have fields := CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span
  refine {s with
    machine := next
    cachedAddress := ?_, present := s.present, tracked := s.tracked
    ghost := ?_, shallow := ?_, race := s.race, backend := ?_
    metadata := ?_, notConstructed := ?_, active := s.active
    unchecked := ?_, noGc := ?_, fixed := s.fixed }
  · unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [fields.terminators]
    exact s.cachedAddress
  · rw [AsMutPtrReturn.accounted_ghost]
    exact s.ghost
  · rw [AsMutPtrReturn.accounted_validation]
    exact s.shallow
  · unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [fields.terminators]
    exact s.backend
  · unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [fields.terminators]
    exact s.metadata
  · unfold next AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [fields.terminators]
    exact s.notConstructed
  · change ((PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.getControl
      ((PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.setControl
        (TerminatorClock.advance ((PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.getControl s.machine.user)) s.machine.user)).checkedArithmetic = false
    rw [CanonicalConfigFacts.actual_term_get_set]
    exact s.unchecked
  · change ((PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.getControl
      ((PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.setControl
        (TerminatorClock.advance ((PreparedContracts.actualConfig s.options () (s.remaining+1) s.span).terminators.getControl s.machine.user)) s.machine.user)).gcInterval = 0
    rw [CanonicalConfigFacts.actual_term_get_set]
    exact s.noGc

def invocation (input : GeneralBorrowForestAsMutInvocation.Input) : GeneralBorrowForestAsMutInvocation.Input := by
  let s := input.start
  have fields := CanonicalConfigFacts.actual_fields s.options () (s.remaining+1) s.span
  refine {input with start := core s, bufferExtras := ?_, cached := ?_, extras := ?_}
  · change (AsMutPtrReturn.accountedMachine s.options s.remaining s.span s.machine).user.payload.payload.user.runtime.extras.allocations.find? _ = _
    unfold AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [fields.terminators]
    exact input.bufferExtras
  · change (AsMutPtrReturn.accountedMachine s.options s.remaining s.span s.machine).user.addresses.baseAddr.find? _ = _
    unfold AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [fields.terminators]
    exact input.cached
  · change (AsMutPtrReturn.accountedMachine s.options s.remaining s.span s.machine).user.payload.payload.user.runtime.extras.allocations.find? _ = _
    unfold AsMutPtrReturn.accountedMachine SourceControl.accounted
    rw [fields.terminators]
    exact input.extras
end
end DuplicatePrefix.GeneralBorrowForestAsMutAccounting
