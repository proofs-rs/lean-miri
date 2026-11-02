import duplicate_prefix.S03IntegerZeroState
import duplicate_prefix.RootZeroInvocationState
import duplicate_prefix.NonliveEmptyRootArgumentScope
import duplicate_prefix.GeneralBorrowWildcardFnEntryRegistration

namespace DuplicatePrefix.S03NonliveZeroState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def argumentsMachine (before : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) : Before :=
  NonliveEmptyRootArgumentScope.resultMachine (RawRootInvocation.machine #[] before) tracker fresh

/-- Nonlive concrete zero FnEntry changes no allocation, but registers its
Strong protector. Fresh-tag formation proves that this new table entry changes
no existing destination permission. The physical packet therefore transports
without requiring a canonical destination tree. -/
def input {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (argumentId : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global) :
    DuplicatePrefixReturnPlaceInput.Input (argumentsMachine before original.tracker fresh) place where
  tracker := (⟨TypedRetagGeneric.protectedGlobal original.tracker.global fresh,original.tracker.retagMode⟩ : MachineHooks.BorrowState)
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
  borrow := Classical.choice (GeneralBorrowWildcardFnEntryRegistration.prepare original.entry.allocation.extra
    original.tracker.global {} argumentId fresh runtime original.source original.selectedRoot original.maximum
    original.offset 1 original.borrow).2.2.2.2.1

theorem model {options : EvalConfigurationCore.Options} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (initial : DuplicatePrefixCallModel.Model options remaining span before)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615) :
    DuplicatePrefixCallModel.Model options (remaining+1) span (argumentsMachine before original.tracker fresh) := by
  have shifted := S03IntegerZeroState.retime initial (remaining+1)
  obtain ⟨tracker,enabled,mode⟩ := initial.defaultTracker
  have same : tracker = original.tracker := Option.some.inj (enabled.symm.trans original.enabled)
  subst tracker
  refine {shifted with
    defaultTracker := ⟨(⟨TypedRetagGeneric.protectedGlobal original.tracker.global fresh,original.tracker.retagMode⟩ : MachineHooks.BorrowState),rfl,mode⟩,
    unchecked := ?_,noGc := ?_}
  · change ((PreparedContracts.actualConfig options () (remaining+1+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).checkedArithmetic = false
    rw [RootZeroInvocationState.raw_control]
    exact shifted.unchecked
  · change ((PreparedContracts.actualConfig options () (remaining+1+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).gcInterval = 0
    rw [RootZeroInvocationState.raw_control]
    exact shifted.noGc

/-- The actual Strong registration preserves complete current runtime facts;
no allocation node is inserted on the nonlive argument path. -/
theorem runtime {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (argumentId : AllocId)
    (initial : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global) :
    DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra
      (TypedRetagGeneric.protectedGlobal original.tracker.global fresh) :=
  (GeneralBorrowWildcardFnEntryRegistration.prepare original.entry.allocation.extra original.tracker.global {}
    argumentId fresh initial original.source original.selectedRoot original.maximum original.offset 1 original.borrow).2.2.2.1

/-- Exact first-argument ledger: one tag is consumed, the Strong table row is
installed, and the entire memory is unchanged. This records the genuine
nonlive transition, not the NoProv transition. -/
theorem ledger (before : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) :
    (argumentsMachine before tracker fresh).memory = before.memory ∧
    (argumentsMachine before tracker fresh).borrowTracker =
      some ⟨TypedRetagGeneric.protectedGlobal tracker.global fresh,tracker.retagMode⟩ ∧
    (TypedRetagGeneric.protectedGlobal tracker.global fresh).nextPointerTag.value.toNat =
      tracker.global.nextPointerTag.value.toNat+1 ∧
    (TypedRetagGeneric.protectedGlobal tracker.global fresh).protectedTags =
      tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector :=
  ⟨rfl,rfl,GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh,rfl⟩

end
end DuplicatePrefix.S03NonliveZeroState
