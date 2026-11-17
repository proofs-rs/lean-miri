import duplicate_prefix.S03SeparateEmptyArgument
import duplicate_prefix.WildcardPoolHitRootArgumentScope
import duplicate_prefix.S04ZeroWildcardRuntime

namespace DuplicatePrefix.S03WildcardArgumentSeparateState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

def argumentsMachine {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slot : WildcardHitPoolRoot.Slot entry.allocation.extra) :=
  WildcardPoolHitRootArgumentScope.resultMachine (RawRootInvocation.machine #[] before) original.tracker fresh id entry slot

/-- A genuine wildcard zero FnEntry changes the other allocation and global
protector table. The complete original return Input is derived internally. -/
def input {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.entry.allocation.extra original.tracker.global)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slot : WildcardHitPoolRoot.Slot entry.allocation.extra) (different : original.id ≠ id) :
    DuplicatePrefixReturnPlaceInput.Input (argumentsMachine original fresh id entry slot) place := by
  let positive := Classical.choice (S03SeparateReturnRegistration.register original.entry.allocation.extra original.tracker.global
    id fresh runtime original.source original.selectedRoot original.maximum original.offset 1 original.borrow).2.1
  exact S03SeparateEmptyArgument.transport original _ (S03LiveEmptyState.next original.tracker fresh) rfl
    (StackPopRelease.lookup_commit_other (RawRootInvocation.machine #[] before).memory id original.id entry original.entry
      (slot.after original.tracker.global.nextPointerTag) different original.live) rfl positive

theorem model {options : EvalConfigurationCore.Options} {remaining : Nat}
    {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (original : DuplicatePrefixReturnPlaceInput.Input before place)
    (initial : DuplicatePrefixCallModel.Model options remaining span before)
    (fresh : original.tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (slot : WildcardHitPoolRoot.Slot entry.allocation.extra) :
    DuplicatePrefixCallModel.Model options (remaining+1) span (argumentsMachine original fresh id entry slot) := by
  have shifted := S03IntegerZeroState.retime initial (remaining+1)
  obtain ⟨tracker,enabled,mode⟩ := initial.defaultTracker
  have same : tracker = original.tracker := Option.some.inj (enabled.symm.trans original.enabled)
  subst tracker
  refine {shifted with defaultTracker := ⟨S03LiveEmptyState.next original.tracker fresh,rfl,mode⟩,unchecked := ?_,noGc := ?_}
  · change ((PreparedContracts.actualConfig options () (remaining+1+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).checkedArithmetic = false
    rw [RootZeroInvocationState.raw_control];exact shifted.unchecked
  · change ((PreparedContracts.actualConfig options () (remaining+1+1) span).terminators.getControl
      (RawRootInvocation.machine #[] before).user).gcInterval = 0
    rw [RootZeroInvocationState.raw_control];exact shifted.noGc

/-- General wildcard zero construction and the later other-allocation return
registration preserve full argument runtime and produce its hidden inactive
leaf. No positive byte observer is required in the argument allocation. -/
theorem facts (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (argumentId returnId : AllocId)
    (first : tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (S03LiveEmptyState.next tracker first).global.nextPointerTag.value < 18446744073709551615)
    (slot : WildcardHitPoolRoot.Slot tree) (room : tree.nodes.size+1 ≤ 4294967295) :
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker (S03LiveEmptyState.next tracker first) second)
      (S03LiveEmptyState.next tracker first).global.nextPointerTag
    DuplicatePrefixBorrowContract.RuntimeFacts (slot.after tracker.global.nextPointerTag) global ∧
    Nonempty (S03EmptyTagState.Data (slot.after tracker.global.nextPointerTag) tracker.global.nextPointerTag slot.index) ∧
    (slot.after tracker.global.nextPointerTag).nodes.size ≤ tree.nodes.size+1 := by
  obtain ⟨_,held,_,registered,_,fresh⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree tracker.global {} argumentId first runtime
  have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag first
  have tagBound : tracker.global.nextPointerTag.value.toNat < (S03LiveEmptyState.next tracker first).global.nextPointerTag.value.toNat := by
    change tracker.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag tracker.global.nextPointerTag first).value.toNat
    omega
  have isHeld : (S03LiveEmptyState.next tracker first).global.protectedTags.contains tracker.global.nextPointerTag = true := by
    exact congrArg Option.isSome held
  have constructed := S04ZeroWildcardRuntime.construct tree (S03LiveEmptyState.next tracker first).global registered
    tracker.global.nextPointerTag fresh room tagBound isHeld 0
  dsimp only at constructed
  rw [slot.child tracker.global.nextPointerTag fresh 0] at constructed
  obtain ⟨_,_,_,after,_,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare (slot.after tracker.global.nextPointerTag)
    (S03LiveEmptyState.next tracker first).global (({} : FrameState).addProtector argumentId tracker.global.nextPointerTag)
    returnId second constructed.2.1
  exact ⟨after,⟨S03EmptyFnEntryFacts.wildcard_data tree slot tracker.global.nextPointerTag fresh
    (DuplicatePrefixBorrowContract.vacant_clean runtime)⟩,constructed.2.2.2⟩

end
end DuplicatePrefix.S03WildcardArgumentSeparateState
