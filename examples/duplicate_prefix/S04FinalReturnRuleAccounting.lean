import duplicate_prefix.S04FinalReturnRuleCopy
import duplicate_prefix.SourceControl

namespace DuplicatePrefix.S04FinalReturnRuleAccounting
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open S04FinalReturnInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def machine (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :=
  (SourceControl.accounted (PreparedContracts.actualConfig options () (remaining+1) span).terminators
    (Storage.withCurrent #[] frame before)).machine

/-- Actual terminator accounting changes source control/clock data only; all
metadata needed by the concrete return destination remains on the same state. -/
theorem metadata (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) :
    (machine options remaining span frame before).user.addresses = before.user.addresses ∧
    (machine options remaining span frame before).user.payload.ghost = before.user.payload.ghost ∧
    (machine options remaining span frame before).user.payload.validation = before.user.payload.validation ∧
    (machine options remaining span frame before).user.payload.payload.user.backend = before.user.payload.payload.user.backend ∧
    (machine options remaining span frame before).user.payload.payload.user.runtime.extras =
      before.user.payload.payload.user.runtime.extras := by
  unfold machine SourceControl.accounted
  rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- Transport permission-free pre-pop metadata across real source accounting. -/
def destination (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (input : Destination before place) :
    Destination (machine options remaining span frame before) place where
  pointer := input.pointer
  physicalPointer := input.physicalPointer
  layout := input.layout
  aligned := input.aligned
  id := input.id
  entry := input.entry
  base := input.base
  offset := input.offset
  capacity := input.capacity
  live := input.live
  pointerAddress := input.pointerAddress
  nonnull := input.nonnull
  addressFits := input.addressFits
  bounds := input.bounds
  size := input.size
  bytes := input.bytes
  mutable := input.mutable
  maskValid := input.maskValid
  maskLength := input.maskLength
  provenanceMap := input.provenanceMap
  borrowSize := input.borrowSize
  tag := input.tag
  parent := input.parent
  concrete := input.concrete
  tagged := input.tagged
  cachedBase := by
    rw [(metadata options remaining span frame before).1]
    exact input.cachedBase

end
end DuplicatePrefix.S04FinalReturnRuleAccounting
