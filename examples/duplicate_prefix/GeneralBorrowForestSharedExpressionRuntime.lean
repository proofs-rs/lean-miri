import duplicate_prefix.GenericFunctionEntryRuntime
import duplicate_prefix.GeneralBorrowForestEntrySharedExpression
namespace DuplicatePrefix.GeneralBorrowForestSharedExpressionRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open ActualReferenceContext CanonicalConfigFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def machine (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree) :=
  {ReferenceBorrowDriver.allocatedMachine before tracker fresh with memory := RetagEntry.updatedMemory before.memory id entry tree}

theorem facts (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (original before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree)
    (runtime : GenericSharedLenAccepted.RuntimeFacts options remaining span original before) :
    GenericSharedLenAccepted.RuntimeFacts options remaining span original (machine before tracker fresh id entry tree) ∧
    GenericSharedLenAccepted.RuntimeFacts options remaining span original
      (PtrMetadataReturn.accountedMachine options remaining span (machine before tracker fresh id entry tree)) := by
  have first : GenericSharedLenAccepted.RuntimeFacts options remaining span original (machine before tracker fresh id entry tree) :=
    ⟨runtime.ghost,runtime.shallow,runtime.race,runtime.addresses,runtime.types,runtime.extras,runtime.backend,
      runtime.unchecked,runtime.noGc,runtime.fixed,runtime.active⟩
  let result := machine before tracker fresh id entry tree
  have data : (RootZeroCompleteState.tick options remaining span result).user.addresses=result.user.addresses ∧
      (RootZeroCompleteState.tick options remaining span result).user.payload.payload.user.types=result.user.payload.payload.user.types ∧
      (RootZeroCompleteState.tick options remaining span result).user.payload.payload.user.runtime.extras=result.user.payload.payload.user.runtime.extras ∧
      (RootZeroCompleteState.tick options remaining span result).user.payload.payload.user.backend=result.user.payload.payload.user.backend := by
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl⟩
  refine ⟨first,?_⟩
  exact ⟨(RootZeroCompleteState.tick_ghost options remaining span result).trans first.ghost,
    (RootZeroCompleteState.tick_shallow options remaining span result).trans first.shallow,
    first.race,data.1.trans first.addresses,data.2.1.trans first.types,data.2.2.1.trans first.extras,
    data.2.2.2.trans first.backend,(RootZeroCompleteState.tick_flags options remaining span result).1.trans first.unchecked,
    (RootZeroCompleteState.tick_flags options remaining span result).2.trans first.noGc,first.fixed,first.active⟩
end
end DuplicatePrefix.GeneralBorrowForestSharedExpressionRuntime
