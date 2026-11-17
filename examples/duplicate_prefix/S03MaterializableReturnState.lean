import duplicate_prefix.S03MaterializableInput
import duplicate_prefix.S03SeparateEmptyArgument
import duplicate_prefix.GlobalEmptyRootPrepared

namespace DuplicatePrefix.S03MaterializableReturnState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Literal common state of image materialization followed by the argument-tree
commit. Concrete and wildcard zero constructors choose different trees. -/
def machine (options : EvalConfigurationCore.Options) (before : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) (tree : BorrowTree) : Before :=
  let prepared := GlobalEmptyRootCopy.preparedMachine options before id root source converted
  {prepared with
    borrowTracker := some (S03LiveEmptyState.next tracker fresh)
    memory := RetagEntry.updatedMemory prepared.memory id (GlobalEmptyRootCopy.entry root source converted) tree}

/-- The exact image/tree update retains every physical return field and its
permission. Fresh protector registration is proved from the initial return
tree's high-water invariant; no renewed Resources or future Input is supplied. -/
def input {options : EvalConfigurationCore.Options} {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (tag : Option BorTag)
    (packet : S03MaterializableInput.Packet options before original.tracker id tag)
    (converted : Allocation Provenance Unit) (tree : BorrowTree) :
    DuplicatePrefixReturnPlaceInput.Input (machine options before original.tracker fresh id packet.root packet.source converted tree) place := by
  let prepared := GlobalEmptyRootCopy.preparedMachine options before id packet.root packet.source converted
  have different := S03MaterializableInput.separate packet original
  have live : prepared.memory.live.find? (fun row => row.1 == original.id) = some (original.id,original.entry) := by
    rw [GlobalEmptyRootPrepared.live_other options before id original.id packet.root packet.source converted different]
    exact original.live
  let positive := Classical.choice (S03SeparateReturnRegistration.register original.entry.allocation.extra original.tracker.global
    id fresh runtime original.source original.selectedRoot original.maximum original.offset 1 original.borrow).2.1
  exact S03SeparateEmptyArgument.transport original _ (S03LiveEmptyState.next original.tracker fresh) rfl
    (StackPopRelease.lookup_commit_other prepared.memory id original.id (GlobalEmptyRootCopy.entry packet.root packet.source converted)
      original.entry tree different live) rfl positive

theorem runtime {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (initial : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615) (id : AllocId) :
    DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra (S03LiveEmptyState.next original.tracker fresh).global :=
  (S03SeparateReturnRegistration.register original.entry.allocation.extra original.tracker.global id fresh initial
    original.source original.selectedRoot original.maximum original.offset 1 original.borrow).1

/-- The current model survives image creation, registration and the exact tree
commit. Metadata, pointer checks and backend policy are retained. -/
theorem model {options : EvalConfigurationCore.Options} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before}
    (initial : DuplicatePrefixCallModel.Model options remaining span before)
    (tracker : MachineHooks.BorrowState) (enabled : before.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit)
    (converted : Allocation Provenance Unit) (tree : BorrowTree) (nextRemaining : Nat) :
    DuplicatePrefixCallModel.Model options nextRemaining span
      (machine options before tracker fresh id root source converted tree) := by
  have shifted := S03IntegerZeroState.retime initial nextRemaining
  obtain ⟨old,oldEnabled,mode⟩ := initial.defaultTracker
  have same : old = tracker := Option.some.inj (oldEnabled.symm.trans enabled)
  subst old
  have controls : (PreparedContracts.actualConfig options () (nextRemaining+1) span).terminators.getControl
      (machine options before tracker fresh id root source converted tree).user =
      (PreparedContracts.actualConfig options () (nextRemaining+1) span).terminators.getControl before.user := by
    rw [(CanonicalConfigFacts.actual_fields options () (nextRemaining+1) span).terminators]
    rfl
  refine {shifted with defaultTracker := ⟨S03LiveEmptyState.next tracker fresh,rfl,mode⟩,unchecked := ?_,noGc := ?_}
  · rw [controls];exact shifted.unchecked
  · rw [controls];exact shifted.noGc

/-- MEMORY and supported STATIC images use exactly this common state. -/
theorem concrete_state (options : EvalConfigurationCore.Options) (before : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit) :
    S03MaterializableArgumentScope.resultMachine options before tracker fresh id root source converted =
      machine options before tracker fresh id root source converted
        (TypedRetagConcreteEmpty.lazyTree root tracker.global.nextPointerTag source.byteSize.bytes) := rfl

theorem wildcard_state (options : EvalConfigurationCore.Options) (before : Before) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (root : BorTag) (source : Allocation CtfeProvenance Unit) (converted : Allocation Provenance Unit) :
    S03MaterializableWildcardScope.resultMachine options before tracker fresh id root source converted =
      machine options before tracker fresh id root source converted
        (WildcardGlobalEmptyReferenceReborrow.finalTree root tracker.global.nextPointerTag source.byteSize) := rfl

end
end DuplicatePrefix.S03MaterializableReturnState
