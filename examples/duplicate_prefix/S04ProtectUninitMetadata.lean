import duplicate_prefix.S04ReturnProtectionInput
import duplicate_prefix.GeneralBorrowRawFnEntryOrder

namespace DuplicatePrefix.S04ProtectUninitMetadata
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open Miri.Input DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Identify the actual protected tree with the raw FnEntry constructor. This
internal bridge derives the order and node bound consumed by the ensuing
Write; it does not require a post-state resource contract. -/
theorem of_retag
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (len : UInt64)
    (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (state : DuplicatePrefixRuntimeInput.OrderedState before tracker)
    (resources : Resources options limits remaining before tracker len)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tree : BorrowTree)
    (actual : TypedRetag.retagPlace (config options remaining span).retag budget place MachineHooks.protectionPolicy
      (Storage.withCurrent frames frame before) =
      .ok (TypedRetagGeneric.retaggedPlace place input.id input.tracker.global.nextPointerTag)
        (ReturnProtection.borrowedState frames frame borrowFrame before input.tracker fresh input.id input.entry tree)) :
    tree.roots.toList.Nodup ∧ GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree ∧
      tree.nodes.size < 65536 ∧
      ∃ child, tree.indexOfTag input.tracker.global.nextPointerTag = some child ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin tree child .Write input.offset (input.offset+1) := by
  obtain ⟨raw,parentTag,offset,length,source,selected,maximum,runtime⟩ :=
    S04ReturnProtection.from_return input state resources tag concrete
  let canonical := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker
    raw.parentTag raw.offset raw.len
  have completed := GeneralBorrowRawFnEntryExecution.completed input.entry.allocation.extra
    input.tracker.global borrowFrame input.id runtime raw
  obtain ⟨ctx⟩ := ActualRetagContext.exists_context options remaining span model.preciseOff model.implicitOff
  have pointer : place.mplace.ptr = Pointer.new (some (.concrete input.id tag)) (Size.ofBytes (input.base+input.offset)) := by
    rw [input.physicalPointer]
    have off : input.pointer.offset = Size.ofBytes (input.base+input.offset) := by
      cases h : input.pointer.offset
      simpa [h,Size.ofBytes] using congrArg Size.ofBytes input.pointerAddress
    simp only [Pointer.withOptionalProvenance,concrete,off,Pointer.new]
  have canonicalActual := S04ReturnProtection.retag_bool_window_from_tree options remaining span ctx budget place
    input.layout frames frame borrowFrame before input.tracker input.enabled frameBorrow fresh input.id input.entry
    input.base input.offset tag pointer input.cachedBase
    (by simpa only [input.size,Size.ofBytes] using input.bounds) input.live model.noDataRace
    _ canonical rfl
    (by simpa only [parentTag,offset,length,TypedBorrowSteps.registeredGlobal,
      ReferenceBorrowDriver.allocatedTracker] using completed.1)
    (by
      have record := S04ReturnProtection.child_record _ completed.2
      simpa only [canonical,GeneralBorrowRawFnEntryArgument.finalTree,parentTag,offset,length,
        GeneralBorrowFreshChild.inside,ChildBorrow.fnEntryLocation,MachineHooks.protectionPolicy,Option.isSome,
        TypedBorrowSteps.registeredGlobal,ReferenceBorrowDriver.allocatedTracker] using record)
  have states := (EStateM.Result.ok.inj (actual.symm.trans canonicalActual)).2
  have trees := congrArg (fun (s : RootState) =>
    (s.machine.memory.live.find? (fun row => row.1 == input.id)).map (fun row => row.2.allocation.extra)) states
  have treeEq : tree = canonical := by
    change ((RetagEntry.updatedMemory before.memory input.id input.entry tree).live.find?
      (fun row => row.1 == input.id)).map (fun row => row.2.allocation.extra) =
      ((RetagEntry.updatedMemory before.memory input.id input.entry canonical).live.find?
      (fun row => row.1 == input.id)).map (fun row => row.2.allocation.extra) at trees
    have lookup (t : BorrowTree) := MemoryCopyBridge.live_lookup_replaced before.memory input.id
      {input.entry with allocation := input.entry.allocation.setExtra t}
    simp only [RetagEntry.updatedMemory,lookup,Option.map_some] at trees
    exact Option.some.inj trees
  rw [treeEq]
  obtain ⟨_,_,growth,roots,_,_,_,child,tagged,_,activity⟩ := GeneralBorrowRawFnEntryResources.resources input.entry.allocation.extra
    input.tracker borrowFrame input.id runtime raw
  have order := GeneralBorrowRawFnEntryOrder.order input.entry.allocation.extra input.tracker
    borrowFrame input.id runtime raw (state.parent_order input.id input.entry input.live)
  have same : tracker = input.tracker := Option.some.inj (state.enabled.symm.trans input.enabled)
  subst tracker
  have member : (input.id,input.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some input.live)
  have room := resources.nodeRoom _ member
  refine ⟨?_,order,?_,child,tagged,?_⟩
  · rw [roots]
    exact state.roots _ member
  · dsimp only at room
    dsimp only [canonical]
    omega
  · simpa only [canonical,offset,length] using activity

end
end DuplicatePrefix.S04ProtectUninitMetadata
