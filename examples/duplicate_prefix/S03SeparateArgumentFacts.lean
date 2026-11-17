import duplicate_prefix.S03SeparateEmptyArgument
import duplicate_prefix.S04ZeroConcreteRuntime

namespace DuplicatePrefix.S03SeparateArgumentFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section

/-- ZERO FnEntry production on an argument allocation, without any positive
byte observer in that allocation. The later return-protector registration
preserves its runtime, and its actual tree is unchanged by the separate store. -/
theorem construct (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (argumentId returnId : AllocId) (parentTag : BorTag)
    (first : tracker.global.nextPointerTag.value < 18446744073709551615)
    (second : (S03LiveEmptyState.next tracker first).global.nextPointerTag.value < 18446744073709551615)
    (slot : ConcreteEmptyPoolEntry.Input tree parentTag tracker.global.nextPointerTag)
    (room : tree.nodes.size+1 ≤ 4294967295) :
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker (S03LiveEmptyState.next tracker first) second)
      (S03LiveEmptyState.next tracker first).global.nextPointerTag
    DuplicatePrefixBorrowContract.RuntimeFacts slot.after global ∧
    Nonempty (S03EmptyTagState.Data slot.after tracker.global.nextPointerTag slot.index) ∧
    slot.after.nodes.size ≤ tree.nodes.size+1 := by
  obtain ⟨_,held,_,registered,_,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare tree tracker.global {} argumentId first runtime
  have successor := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag first
  have tagBound : tracker.global.nextPointerTag.value.toNat < (S03LiveEmptyState.next tracker first).global.nextPointerTag.value.toNat := by
    change tracker.global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag tracker.global.nextPointerTag first).value.toNat
    omega
  have isHeld : (S03LiveEmptyState.next tracker first).global.protectedTags.contains tracker.global.nextPointerTag = true := by
    change ((GeneralBorrowFnEntryRegistration.registered tracker.global {} argumentId first).1.protectedTags.get
      tracker.global.nextPointerTag).isSome = true
    rw [held]
    rfl
  have current := S04ZeroConcreteRuntime.construct tree (S03LiveEmptyState.next tracker first).global registered
    parentTag slot.parent slot.parentNode slot.tagged slot.present tracker.global.nextPointerTag slot.fresh room tagBound isHeld 0
  rw [slot.child 0] at current
  obtain ⟨_,_,_,after,_,_⟩ := GeneralBorrowFnEntryRegistrationRuntime.prepare slot.after (S03LiveEmptyState.next tracker first).global
    (({} : FrameState).addProtector argumentId tracker.global.nextPointerTag) returnId second current.2.1
  exact ⟨after,⟨S03EmptyFnEntryFacts.concrete_data _ _ _ slot⟩,current.2.2.2⟩

end
end DuplicatePrefix.S03SeparateArgumentFacts
