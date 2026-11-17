import duplicate_prefix.S03FinalReturnInputBounds
import duplicate_prefix.S04FinalReturnRuleAccounting
namespace DuplicatePrefix.S03FinalReturnAccountingBounds
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
noncomputable section
/-- Transport permission-free pre-pop metadata across real source accounting. -/
def destination (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (input : S03FinalReturnInputBounds.Destination before place) :
    S03FinalReturnInputBounds.Destination (S04FinalReturnRuleAccounting.machine options remaining span frame before) place where
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
  pointerBounds := input.pointerBounds
  borrowSize := input.borrowSize
  tag := input.tag
  parent := input.parent
  concrete := input.concrete
  tagged := input.tagged
  cachedBase := by
    rw [(S04FinalReturnRuleAccounting.metadata options remaining span frame before).1]
    exact input.cachedBase

end
end DuplicatePrefix.S03FinalReturnAccountingBounds
