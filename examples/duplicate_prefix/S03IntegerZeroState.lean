import duplicate_prefix.S03ReturnProtectionRaw
import duplicate_prefix.RootZeroInvocationState

namespace DuplicatePrefix.S03IntegerZeroState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def argumentsMachine (before : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) : Before :=
  ReferenceBorrowDriver.allocatedMachine (RawRootInvocation.machine #[] before) tracker fresh

/-- No-provenance zero FnEntry consumes a fresh global tag but does not install
a tree or protector. The original concrete destination's physical metadata and
Positive therefore form its current Input directly. -/
def input {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615) :
    DuplicatePrefixReturnPlaceInput.Input (argumentsMachine before original.tracker fresh) place where
  tracker := ReferenceBorrowDriver.allocatedTracker original.tracker fresh
  enabled := rfl
  pointer := original.pointer
  physicalPointer := original.physicalPointer
  layout := original.layout
  aligned := original.aligned
  id := original.id
  entry := original.entry
  base := original.base
  offset := original.offset
  capacity := original.capacity
  live := original.live
  cachedBase := original.cachedBase
  pointerAddress := original.pointerAddress
  nonnull := original.nonnull
  addressFits := original.addressFits
  bounds := original.bounds
  size := original.size
  bytes := original.bytes
  mutable := original.mutable
  maskValid := original.maskValid
  maskLength := original.maskLength
  provenanceMap := original.provenanceMap
  borrowSize := original.borrowSize
  source := original.source
  selectedRoot := original.selectedRoot
  maximum := original.maximum
  binding := original.binding
  borrow := original.borrow

theorem retime {options : EvalConfigurationCore.Options} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before}
    (model : DuplicatePrefixCallModel.Model options remaining span before) (next : Nat) :
    DuplicatePrefixCallModel.Model options next span before := by
  have controls : (PreparedContracts.actualConfig options () (next+1) span).terminators.getControl =
      (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl := by
    rw [(CanonicalConfigFacts.actual_fields options () (next+1) span).terminators,
      (CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
  refine {model with unchecked := ?_,noGc := ?_}
  · rw [controls]
    exact model.unchecked
  · rw [controls]
    exact model.noGc

theorem model {options : EvalConfigurationCore.Options} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (initial : DuplicatePrefixCallModel.Model options remaining span before)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615) :
    DuplicatePrefixCallModel.Model options (remaining+1) span (argumentsMachine before original.tracker fresh) := by
  have shifted := retime initial (remaining+1)
  obtain ⟨tracker,enabled,mode⟩ := initial.defaultTracker
  have same : tracker = original.tracker := Option.some.inj (enabled.symm.trans original.enabled)
  subst tracker
  refine {shifted with
    defaultTracker := ⟨ReferenceBorrowDriver.allocatedTracker original.tracker fresh,rfl,mode⟩,
    unchecked := ?_,noGc := ?_}
  · change ((PreparedContracts.actualConfig options () (remaining+1+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).checkedArithmetic = false
    rw [RootZeroInvocationState.raw_control]
    exact shifted.unchecked
  · change ((PreparedContracts.actualConfig options () (remaining+1+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).gcInterval = 0
    rw [RootZeroInvocationState.raw_control]
    exact shifted.noGc

theorem runtime {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (initial : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global) :
    DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra
      (ReferenceBorrowDriver.allocatedTracker original.tracker fresh).global := by
  have successor := GenericFunctionEntryNumerics.successor_value original.tracker.global.nextPointerTag fresh
  refine {initial with below := ⟨?_,?_⟩}
  · intro row member
    have old := initial.below.mapping row member
    change row.1.value.toNat < (TypedRetagEmpty.successorTag original.tracker.global.nextPointerTag fresh).value.toNat
    omega
  · intro row member
    have old := initial.below.protectors row member
    change row.1.value.toNat < (TypedRetagEmpty.successorTag original.tracker.global.nextPointerTag fresh).value.toNat
    omega

end
end DuplicatePrefix.S03IntegerZeroState
