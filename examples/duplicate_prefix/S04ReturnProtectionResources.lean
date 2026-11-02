import duplicate_prefix.S04ReturnProtection

namespace DuplicatePrefix.S04ReturnProtectionResources
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
open DuplicatePrefixCallSpecification S04ReturnProtection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Real protected return-slot retag, for a concrete destination in a general
allocation/tree and at any valid byte offset. The old byte is not read. -/
theorem invoke_concrete
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (len : UInt64)
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (state : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (resources : Resources options limits remaining before tracker len)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame) :
    ∃ (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
      (finalTree : BorrowTree),
      TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
        (Storage.withCurrent frames frame before) =
        .ok (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)
          (borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry finalTree) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts finalTree
        (registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag) ∧
      finalTree.locations.size = input.entry.allocation.extra.locations.size ∧
      finalTree.nodes.size ≤ input.entry.allocation.extra.nodes.size+1 ∧
      ∃ child selected,
        input.selectedRoot = some selected ∧
        finalTree.indexOfTag input.tracker.global.nextPointerTag = some child ∧
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive finalTree
          (registeredGlobal (allocatedTracker input.tracker fresh) input.tracker.global.nextPointerTag).protectedTags
          (some child) (some selected) input.maximum input.offset 1) := by
  obtain ⟨ctx⟩ := ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff
  obtain ⟨raw,parentTag,offset,length,source,selected,maximum,runtime⟩ := from_return input state resources tag concrete
  obtain ⟨output,actual,outputTag,global,frameEq,readDone,childDone,afterRuntime,capacity,growth,
    child,lookup,roots,⟨positive⟩,activity⟩ :=
    GeneralBorrowRawFnEntry.invoke_positive input.entry.allocation.extra input.tracker.global borrowFrame input.id runtime raw
  have shape := actual
  simp only [GeneralBorrowForestFnEntry.operation,TypedRetagEmpty.allocate_tag input.tracker.global raw.tagRoom,
    Except.bind,Except.pure,bind,pure] at shape
  have outputEq := Except.ok.inj shape
  subst output
  have pointer : place.mplace.ptr = Pointer.new (some (.concrete input.id tag)) (Size.ofBytes (input.base+input.offset)) := by
    have addr := input.pointerAddress
    have ptrEq : input.pointer = Pointer.new (.concrete input.id tag) (Size.ofBytes (input.base+input.offset)) := by
      cases h : input.pointer with
      | mk off prov =>
        cases off with
        | mk bytes =>
          simp only [h,Pointer.provenance] at concrete
          simp only [h,Pointer.offset,Size.bytes] at addr
          cases concrete
          cases addr
          rfl
    rw [input.physicalPointer,ptrEq]
    rfl
  let accessed := GeneralBorrowForestProtected.read input.entry.allocation.extra
    (GeneralBorrowFnEntryRegistration.registered input.tracker.global borrowFrame input.id raw.tagRoom).1.protectedTags
    raw.parentTag raw.offset raw.len .VisitChildrenOfAccessed
  let final := accessed.tree.newChild (Size.ofBytes raw.offset) (.concrete raw.parentTag)
    input.tracker.global.nextPointerTag (DedupRangeMap.new (Size.ofBytes raw.len) GeneralBorrowFreshChild.inside)
    (.ReservedFrz false) true
  refine ⟨raw.tagRoom,final.tree,?_,?_,?_,?_,child,raw.selected,selected,?_,?_⟩
  · apply retag_bool_window_from_tree options remaining span ctx budget place input.layout frames frame borrowFrame
      before input.tracker input.enabled frameBorrow raw.tagRoom input.id input.entry input.base input.offset tag pointer
      input.cachedBase (by simpa only [input.size,Size.ofBytes] using input.bounds) input.live model.noDataRace accessed.tree final.tree
    · simp only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome]
    · simpa only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using readDone
    · have eq := child_record _ childDone
      simpa only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using eq
  · simpa only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using afterRuntime
  · simpa only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using capacity
  · simpa only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using growth
  · simpa only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using lookup
  · simpa only [final,accessed,parentTag,offset,length,maximum,GeneralBorrowForestProtected.read,GeneralBorrowFnEntryRegistration.registered,GeneralBorrowFnEntryRegistration.advanced,GlobalState.addProtector,registeredGlobal,allocatedTracker,GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome] using (show Nonempty _ from ⟨positive⟩)

end
end DuplicatePrefix.S04ReturnProtectionResources
