import duplicate_prefix.GeneralBorrowRawFnEntryResources
import duplicate_prefix.GeneralBorrowFnEntryRegistration
import duplicate_prefix.TypedRetagGeneric
namespace DuplicatePrefix.GeneralBorrowRawRootEntryResources
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The ROOT initializer registers its return-slot protector after the buffer
argument. This second, fresh registration preserves the derived buffer owner
packet and runtime; it requires tag headroom, not future permissions. -/
theorem resources (tree : BorrowTree) (tracker : MachineHooks.BorrowState)
    (frame : FrameState) (buffer slot : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (slotRoom : (TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom).nextPointerTag.value < 18446744073709551615) :
    let finalTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let argumentGlobal := TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom
    let fullGlobal := (GeneralBorrowFnEntryRegistration.registered argumentGlobal
      (frame.addProtector buffer tracker.global.nextPointerTag) slot slotRoom).1
    DuplicatePrefixBorrowContract.RuntimeFacts finalTree fullGlobal ∧
    finalTree.locations.size = tree.locations.size ∧ finalTree.nodes.size ≤ tree.nodes.size+1 ∧
    finalTree.roots = tree.roots ∧
    fullGlobal.protectedTags.get argumentGlobal.nextPointerTag = some .StrongProtector ∧
    GeneralBorrowTagMap.Fresh finalTree.tagMapping argumentGlobal.nextPointerTag ∧
    ∃ child, finalTree.indexOfTag tracker.global.nextPointerTag = some child ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree fullGlobal.protectedTags
        (some child) (some input.selected) input.maximum input.offset input.len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin finalTree child .Write input.offset (input.offset+input.len) := by
  obtain ⟨current,capacity,growth,roots,held,framePush,fresh,child,lookup,⟨positive⟩,activity⟩ :=
    GeneralBorrowRawFnEntryResources.resources tree tracker frame buffer runtime input
  have globalEq : TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom)
      tracker.global.nextPointerTag = TypedRetagGeneric.protectedGlobal tracker.global input.tagRoom := rfl
  rw [globalEq] at current positive
  obtain ⟨allocated,slotHeld,slotFrame,afterRuntime,afterPositive,slotFresh⟩ :=
    GeneralBorrowFnEntryRegistration.prepare _ _ (frame.addProtector buffer tracker.global.nextPointerTag)
      slot slotRoom current child input.selected input.maximum input.offset input.len positive
  exact ⟨afterRuntime,capacity,growth,roots,slotHeld,slotFresh,child,lookup,afterPositive,activity⟩
end DuplicatePrefix.GeneralBorrowRawRootEntryResources
