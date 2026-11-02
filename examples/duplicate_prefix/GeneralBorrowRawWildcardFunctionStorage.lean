import duplicate_prefix.GeneralBorrowRawWildcardFunctionState
import duplicate_prefix.RootZeroCompleteState
namespace DuplicatePrefix.GeneralBorrowRawWildcardFunctionStorage
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowRawWildcardFunctionState
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- At the actual post-initializer tick the live buffer has exactly the derived
tree and original physical allocation data. Return-slot writes do not disturb
it; the tracker is exactly the two-protector tracker used by full Positive. -/
theorem current (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (buffer : AllocId) (bufferEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (finalTree : BorrowTree)
    (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree) (separate : buffer ≠ slot) :
    let entered := enteredMachine machine tracker fresh buffer bufferEntry finalTree fresh2 slot slotEntry slotRoot updated
    let actual := RootZeroCompleteState.tick options remaining span entered
    actual.memory = entered.memory ∧
    actual.memory.live.find? (fun row => row.1 == buffer) =
      some (buffer,{bufferEntry with allocation := bufferEntry.allocation.setExtra finalTree}) ∧
    actual.borrowTracker = some (held tracker fresh fresh2) ∧
    actual.user.addresses = machine.user.addresses := by
  dsimp only
  have memory : (RootZeroCompleteState.tick options remaining span
      (enteredMachine machine tracker fresh buffer bufferEntry finalTree fresh2 slot slotEntry slotRoot updated)).memory =
      (enteredMachine machine tracker fresh buffer bufferEntry finalTree fresh2 slot slotEntry slotRoot updated).memory := by
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] <;> rfl
  refine ⟨memory,?_,?_,?_⟩
  · rw [memory]
    exact buffer_lookup machine tracker fresh buffer bufferEntry finalTree fresh2 slot slotEntry slotRoot updated separate
  · unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] <;> rfl
  · unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators] <;> rfl
end DuplicatePrefix.GeneralBorrowRawWildcardFunctionStorage
