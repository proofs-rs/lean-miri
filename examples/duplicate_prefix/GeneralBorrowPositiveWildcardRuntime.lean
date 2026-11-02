import duplicate_prefix.GeneralBorrowPositiveWildcardFunctionState
import duplicate_prefix.GenericSharedLenAccepted
import duplicate_prefix.PushThread

namespace DuplicatePrefix.GeneralBorrowPositiveWildcardRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowPositiveWildcardFunctionState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

set_option autoImplicit false in
/-- All runtime flags needed by the accepted shared prefix are transported from
before the genuine ROOT invocation. No post-entry flag or thread premise is used. -/
theorem facts
    (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (buffer : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (len : UInt64) (fresh2 : (next tracker fresh).global.nextPointerTag.value < 18446744073709551615)
    (slot : AllocId) (slotEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (slotRoot : BorTag)
    (updated : Allocation Provenance BorrowTree)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (race : before.dataRace = none) (backend : before.user.payload.payload.user.backend = .none)
    (thread : ThreadRecord) (active : before.threads.activeThread? = some thread)
    (unchecked : ((config options (remaining+1) span).terminators.getControl before.user).checkedArithmetic = false)
    (noGc : ((config options (remaining+1) span).terminators.getControl before.user).gcInterval = 0)
    (fixed : before.threads.fixedScheduling = true) :
    let entered := enteredMachine (RawRootInvocation.machine #[] before) tracker fresh buffer entry len
      fresh2 slot slotEntry slotRoot updated
    GenericSharedLenAccepted.RuntimeFacts options remaining span before (RootZeroCompleteState.tick options remaining span entered) := by
  let raw := RawRootInvocation.machine #[] before
  let entered := enteredMachine raw tracker fresh buffer entry len fresh2 slot slotEntry slotRoot updated
  let after := RootZeroCompleteState.tick options remaining span entered
  have rawFacts := RawRootInvocation.preservation #[] before
  have tick : after.user.addresses = entered.user.addresses ∧
      after.user.payload.payload.user.types = entered.user.payload.payload.user.types ∧
      after.user.payload.payload.user.runtime.extras = entered.user.payload.payload.user.runtime.extras ∧
      after.user.payload.payload.user.backend = entered.user.payload.payload.user.backend ∧
      after.user.payload.ghost = entered.user.payload.ghost ∧ after.user.payload.validation = entered.user.payload.validation ∧
      after.dataRace = entered.dataRace ∧ after.threads = entered.threads := by
    unfold after RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have control : ((config options (remaining+1) span).terminators.getControl after.user).checkedArithmetic =
      ((config options (remaining+1) span).terminators.getControl before.user).checkedArithmetic ∧
      ((config options (remaining+1) span).terminators.getControl after.user).gcInterval =
      ((config options (remaining+1) span).terminators.getControl before.user).gcInterval := by
    unfold after RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl⟩
  have activeRaw : raw.threads.activeThread? = some {thread with topUserRelevantFrame := some 0} :=
    PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 active
  refine ⟨tick.2.2.2.2.1.trans (rawFacts.2.2.2.2.1.trans ghost),
    tick.2.2.2.2.2.1.trans (rawFacts.2.2.2.2.2.1.trans shallow),
    tick.2.2.2.2.2.2.1.trans (rawFacts.2.2.1.trans race),
    tick.1.trans rawFacts.2.2.2.1,tick.2.1.trans rawFacts.2.2.2.2.2.2.1,
    tick.2.2.1.trans rawFacts.2.2.2.2.2.2.2.2,
    tick.2.2.2.1.trans (rawFacts.2.2.2.2.2.2.2.1.trans backend),?_,?_,?_,?_⟩
  · rw [control.1]
    exact unchecked
  · rw [control.2]
    exact noGc
  · rw [tick.2.2.2.2.2.2.2]
    exact fixed
  · refine ⟨{thread with topUserRelevantFrame := some 0},?_,rfl⟩
    rw [tick.2.2.2.2.2.2.2]
    exact activeRaw

end DuplicatePrefix.GeneralBorrowPositiveWildcardRuntime
