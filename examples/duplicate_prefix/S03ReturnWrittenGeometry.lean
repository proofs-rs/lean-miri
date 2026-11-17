import duplicate_prefix.S03ReturnChildMetadata
import duplicate_prefix.S03ReturnProtectionRaw

namespace DuplicatePrefix.S03ReturnWrittenGeometry
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Physical geometry of the actual protected constructor and successful Write.
Only the constructor consumes node room; ranged access preserves its metadata. -/
theorem run (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (id : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowRawFnEntry.Input tree tracker.global)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree)
    (headroom : tree.nodes.size+1 < 65536) :
    let protectedTree := GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
    let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom)
      tracker.global.nextPointerTag
    let written := (protectedTree.performBorrowAccessRange (.concrete tracker.global.nextPointerTag)
      (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write global.protectedTags .VisitChildrenOfAccessed).tree
    written.locations.size = tree.locations.size ∧ written.roots.toList.Nodup ∧ written.nodes.size < 65536 := by
  obtain ⟨post,capacity,growth,roots,_,_,_,child,tagged,⟨positive⟩,activity⟩ :=
    GeneralBorrowRawFnEntryResources.resources tree tracker frame id runtime input
  have postOrder := GeneralBorrowRawFnEntryOrder.order tree tracker frame id runtime input order
  have short : (GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len).nodes.size < 65536 := by omega
  have distinct : (GeneralBorrowRawFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len).roots.toList.Nodup := by
    rw [roots];exact input.distinct
  obtain ⟨contract,_,_⟩ := GeneralBorrowConcreteRowReadRange.access_runtime_kind _ _ post _ child input.selected
    input.maximum tagged (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write .VisitChildrenOfAccessed
    input.offset input.len positive distinct (fun _ _ => postOrder) short (Nat.le_refl _) (Nat.le_refl _)
  exact ⟨contract.capacity.trans capacity,by rw [contract.roots];exact distinct,by rw [contract.nodes];exact short⟩

end DuplicatePrefix.S03ReturnWrittenGeometry
