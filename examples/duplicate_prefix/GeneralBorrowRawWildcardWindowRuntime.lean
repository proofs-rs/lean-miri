import duplicate_prefix.GeneralBorrowRawWildcardWindowInitial
import duplicate_prefix.GeneralBorrowFreshRootScopedRootZeroPhysical
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowRawWildcardWindowInitial
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

private theorem untick (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (facts : GenericSharedLenAccepted.RuntimeFacts options remaining span before (RootZeroCompleteState.tick options remaining span machine)) :
    GenericSharedLenAccepted.RuntimeFacts options remaining span before machine := by
  have data : (RootZeroCompleteState.tick options remaining span machine).user.addresses=machine.user.addresses ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.types=machine.user.payload.payload.user.types ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.backend=machine.user.payload.payload.user.backend := by
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl⟩
  exact ⟨(RootZeroCompleteState.tick_ghost options remaining span machine).symm.trans facts.ghost,
    (RootZeroCompleteState.tick_shallow options remaining span machine).symm.trans facts.shallow,
    facts.race,data.1.symm.trans facts.addresses,data.2.1.symm.trans facts.types,data.2.2.1.symm.trans facts.extras,
    data.2.2.2.symm.trans facts.backend,
    (RootZeroCompleteState.tick_flags options remaining span machine).1.symm.trans facts.unchecked,
    (RootZeroCompleteState.tick_flags options remaining span machine).2.symm.trans facts.noGc,facts.fixed,facts.active⟩

theorem facts (s : Initial) (output : GeneralBorrowForestFnEntry.Output) (allocation : Allocation Provenance BorrowTree) :
    GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before (machine s output allocation) := by
  have old := untick s.options s.remaining s.span s.before _
    (GenericFunctionEntryRuntime.facts s.options s.remaining s.span s.before s.tracker s.fresh s.id s.entry s.tracker.global.nextPointerTag (offset s) s.len
      s.slotFresh s.slotId s.slotEntry s.slotRoot allocation s.ghost s.shallow s.race s.noBackend s.thread s.active s.unchecked s.noGc s.fixed)
  exact ⟨old.ghost,old.shallow,old.race,old.addresses,old.types,old.extras,old.backend,old.unchecked,old.noGc,old.fixed,old.active⟩

theorem tick_facts (s : Initial) (output : GeneralBorrowForestFnEntry.Output) (allocation : Allocation Provenance BorrowTree) :
    GenericSharedLenAccepted.RuntimeFacts s.options s.remaining s.span s.before (RootZeroCompleteState.tick s.options s.remaining s.span (machine s output allocation)) := by
  have old := GenericFunctionEntryRuntime.facts s.options s.remaining s.span s.before s.tracker s.fresh s.id s.entry s.tracker.global.nextPointerTag (offset s) s.len
      s.slotFresh s.slotId s.slotEntry s.slotRoot allocation s.ghost s.shallow s.race s.noBackend s.thread s.active s.unchecked s.noGc s.fixed
  exact ⟨old.ghost,old.shallow,old.race,old.addresses,old.types,old.extras,old.backend,old.unchecked,old.noGc,old.fixed,old.active⟩

end
end DuplicatePrefix.GeneralBorrowRawWildcardWindowRuntime
