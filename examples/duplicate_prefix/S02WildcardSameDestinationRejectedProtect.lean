import duplicate_prefix.S02SameDestinationZeroCore
import duplicate_prefix.S02SameAllocationProtectSource
import duplicate_prefix.S02ProtectUninitOldActivity
import duplicate_prefix.S03ReturnProtectionMetadata

namespace DuplicatePrefix.S02WildcardSameDestinationRejectedProtect
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Current disjoint source and destination data suffice for actual protection
and the count-zero return packet. The source may be a parentless wildcard child. -/
theorem invoke
    {options : EvalConfigurationCore.Options} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
    (budget : Nat) (before : Before) (model : DuplicatePrefixCallModel.Model options remaining span before)
    (place : MPlaceTy Provenance) (input : DuplicatePrefixReturnPlaceInput.Input before place)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts input.entry.allocation.extra input.tracker.global)
    (distinct : input.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder input.entry.allocation.extra)
    (headroom : input.entry.allocation.extra.nodes.size+1 < 65536)
    (fresh : input.tracker.global.nextPointerTag.value < 18446744073709551615)
    (tag : BorTag) (concrete : input.pointer.provenance = .concrete input.id tag)
    (frame : CompilerFrameContext.ActualFrame) (owned : FrameState)
    (frameBorrow : frame.extra.borrowTracker = some owned)
    (extras : before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == input.id) =
      some (input.id,⟨none,#[]⟩))
    (sourceTag : BorTag) (sourceChild sourceSelected : UniIndex) (sourceMaximum : Option BorTag)
    (sourceOffset sourceLen : UInt64) (sourceBefore : TreeNode)
    (sourceTagged : input.entry.allocation.extra.indexOfTag sourceTag = some sourceChild)
    (sourcePresent : input.entry.allocation.extra.nodeAt sourceChild = some sourceBefore)
    (sourceSame : sourceBefore.tag = sourceTag)
    (sourceLeaf : sourceBefore.children = #[])
    (sourceHidden : sourceBefore.isExposed = false)
    (sourcePositive : DuplicatePrefixBorrowAuthorization.Positive input.entry.allocation.extra input.tracker.global.protectedTags
      (some sourceChild) (some sourceSelected) sourceMaximum sourceOffset sourceLen)
    (sourceActivity : GeneralBorrowFreshActiveWithin.ActiveWithin input.entry.allocation.extra sourceChild .Write
      sourceOffset (sourceOffset+sourceLen))
    (notSourceParent : input.source ≠ some sourceChild)
    (disjoint : input.offset.toNat+1 ≤ sourceOffset.toNat ∨ (sourceOffset+sourceLen).toNat ≤ input.offset.toNat)
    (ownedSource : owned.protectedTags = #[(input.id,sourceTag)]) :
    let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
    ∃ updated,
      TypedRetag.protectInPlaceFunctionArgument (config options remaining span).retag budget place
        (Storage.withCurrent #[] frame before) =
        .ok () (S04ProtectUninit.finished before place input #[] frame owned fresh tree updated) ∧
      ∃ packet : S02SameDestinationZeroCore.Packet
        (CallEntryFacts.doneRootFrame
          {TypedBorrowSteps.registeredFrame frame owned input.id input.tracker.global.nextPointerTag with
            location := .unwinding ⟨559⟩})
        (S04ProtectUninit.finished before place input #[] frame owned fresh tree updated).machine place,
        packet.sourceTag = sourceTag ∧ packet.sourceChild = sourceChild ∧ packet.sourceSelected = sourceSelected ∧
        packet.sourceMaximum = sourceMaximum ∧ packet.sourceOffset = sourceOffset ∧ packet.sourceLen = sourceLen ∧
        packet.sourceNode.tag = sourceTag ∧ packet.destination.id = input.id ∧
        packet.destination.entry = {input.entry with allocation := updated} ∧
        packet.returnTag = input.tracker.global.nextPointerTag ∧
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder updated.extra ∧
        updated.extra.nodes.size ≤ input.entry.allocation.extra.nodes.size+1 ∧
        updated.extra = (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
          (Size.ofBytes input.offset) (Size.ofBytes 1) .Write
          (TypedRetagGeneric.protectedGlobal input.tracker.global fresh).protectedTags .VisitChildrenOfAccessed).tree := by
  dsimp only
  obtain ⟨raw,parentTag,offset,length,selected,maximum⟩ :=
    S03ReturnProtectionRaw.packet input runtime distinct order headroom fresh tag concrete
  have sourceAfter := S02SameAllocationProtectSource.positive before place input runtime distinct order headroom fresh tag concrete
    (some sourceChild) (some sourceSelected) sourceMaximum sourceOffset sourceLen disjoint sourcePositive
  obtain ⟨updated,protect,extra,bytes,len,mutable,maskWf,maskLen,pointers,post,postOrder,
      child,tagged,positive,activity⟩ := S03ReturnProtectionMetadata.invoke_concrete
    budget before model place input runtime distinct order headroom fresh tag concrete #[] frame owned frameBorrow
    #[] extras (by simp)
  have binding := input.binding
  simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
  obtain ⟨_,parent,parentSource,parentTagged⟩ := binding
  have parentEq : parent = raw.parent := by
    have h := raw.tagged
    rw [parentTag] at h
    exact Option.some.inj (parentTagged.symm.trans h)
  have different : sourceChild ≠ raw.parent := by
    intro same
    apply notSourceParent
    rw [parentSource,parentEq,←same]
  obtain ⟨oldTagged,sourceNode,oldPresent,oldTag,oldHidden⟩ :=
    S02ProtectUninitNodes.old_node input.entry.allocation.extra input.tracker owned input.id
      runtime raw sourceChild sourceBefore sourcePresent sourceTag sourceTagged
  obtain ⟨metadataChild,node,newTagged,present,same,edge,leaf,hidden⟩ :=
    S02ProtectUninitNodes.new_node input.entry.allocation.extra input.tracker owned input.id runtime raw
  have sourceActive := S02ProtectUninitOldActivity.preserved input.entry.allocation.extra input.tracker owned input.id
    runtime raw sourceChild sourceBefore sourcePresent sourceLeaf sourceHidden different
    sourceOffset (sourceOffset+sourceLen) sourceActivity
  have resources := GeneralBorrowRawFnEntryResources.resources input.entry.allocation.extra input.tracker owned input.id runtime raw
  have writtenFrame := GeneralBorrowFreshReadFrame.frame
    (GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1)
    (.concrete input.tracker.global.nextPointerTag) (Size.ofBytes input.offset) (Size.ofBytes 1) .Write
    (TypedRetagGeneric.protectedGlobal input.tracker.global fresh).protectedTags .VisitChildrenOfAccessed
  simp only [parentTag,offset,length] at oldTagged oldPresent newTagged present sourceActive resources
  have childEq : metadataChild = child := Option.some.inj (newTagged.symm.trans tagged)
  subst metadataChild
  have tagBelow := GeneralBorrowForestTagHighWater.mapped input.entry.allocation.extra input.tracker.global.protectedTags
    input.tracker.global.nextPointerTag sourceTag runtime.below sourceChild sourceTagged
  have tagDifferent : sourceTag ≠ input.tracker.global.nextPointerTag := by
    intro same
    rw [same] at tagBelow
    omega
  have childrenDifferent : child ≠ sourceChild := by
    intro equal
    rw [equal] at present
    have nodeEq : node = sourceNode := Option.some.inj (present.symm.trans oldPresent)
    exact tagDifferent ((oldTag.trans sourceSame).symm.trans ((congrArg TreeNode.tag nodeEq).symm.trans same))
  let tree := GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1
  let global := TypedBorrowSteps.registeredGlobal (ReferenceBorrowDriver.allocatedTracker input.tracker fresh)
    input.tracker.global.nextPointerTag
  let written := (tree.performBorrowAccessRange (.concrete input.tracker.global.nextPointerTag)
    (Size.ofBytes input.offset) (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
  have writtenRoots := congrArg BorrowTree.roots writtenFrame
  have writtenNodes := congrArg BorrowTree.nodes writtenFrame
  change written.roots = tree.roots at writtenRoots
  change written.nodes = tree.nodes at writtenNodes
  have roots : written.roots.toList.Nodup := by
    rw [writtenRoots, resources.2.2.2.1]
    exact distinct
  have short : written.nodes.size < 65536 := by
    rw [writtenNodes]
    have growth := resources.2.2.1
    change (GeneralBorrowRawFnEntryArgument.finalTree input.entry.allocation.extra input.tracker tag input.offset 1).nodes.size < 65536
    omega
  have shape := S02SeparateDestinationWrittenShape.run input runtime distinct order headroom fresh tag concrete
  let physical := S02SeparateDestinationPhysical.of_protection input tag concrete #[] frame owned fresh tree updated written
    extra bytes len mutable maskWf maskLen pointers shape.1 shape.2
  let after := S04ProtectUninit.finished before place input #[] frame owned fresh tree updated
  let installed := CallEntryFacts.doneRootFrame
    {TypedBorrowSteps.registeredFrame frame owned input.id input.tracker.global.nextPointerTag with location := .unwinding ⟨559⟩}
  let borrowFrame := owned.addProtector input.id input.tracker.global.nextPointerTag
  let tracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker input.tracker fresh)
    input.tracker.global.nextPointerTag
  have physicalEntry : physical.entry = {input.entry with allocation := updated} := rfl
  have physicalOffset : physical.offset = input.offset := rfl
  have physicalId : physical.id = input.id := rfl
  have physicalParent : physical.parent = raw.parent := by
    have h := physical.tagged
    change updated.extra.indexOfTag tag = some physical.parent at h
    rw [extra,shape.2] at h
    exact Option.some.inj (h.symm.trans (by rw [←parentTag]; exact raw.tagged))
  have ownedTags : borrowFrame.protectedTags =
      #[(physical.id,sourceTag),(physical.id,input.tracker.global.nextPointerTag)] := by
    change owned.protectedTags.push (input.id,input.tracker.global.nextPointerTag) = _
    rw [ownedSource]
    rfl
  have runtimePhysical : DuplicatePrefixBorrowContract.RuntimeFacts physical.entry.allocation.extra tracker.global := by
    rw [physicalEntry,extra]
    exact post
  have sourceTaggedPhysical : physical.entry.allocation.extra.indexOfTag sourceTag = some sourceChild := by
    rw [physicalEntry,extra]
    exact oldTagged
  have sourcePresentPhysical : physical.entry.allocation.extra.nodeAt sourceChild = some sourceNode := by
    rw [physicalEntry,extra]
    exact oldPresent
  have sourceHiddenAfter : sourceNode.isExposed = false := oldHidden.trans sourceHidden
  have taggedPhysical : physical.entry.allocation.extra.indexOfTag input.tracker.global.nextPointerTag = some child := by
    rw [physicalEntry,extra]
    exact tagged
  have presentPhysical : physical.entry.allocation.extra.nodeAt child = some node := by
    rw [physicalEntry,extra]
    exact present
  have hiddenFrame := S02SameDestinationHiddenFrame.of_hidden physical.entry.allocation.extra tracker.global borrowFrame
    physical.id physical.id sourceTag input.tracker.global.nextPointerTag child node ownedTags
    runtimePhysical sourceChild sourceNode sourceTaggedPhysical sourcePresentPhysical sourceHiddenAfter
    taggedPhysical presentPhysical hidden
  have returnStop : (physical.offset+1).toNat = physical.offset.toNat+1 := by
    have bound : physical.offset.toNat+1 < 2^64 := Nat.lt_of_le_of_lt physical.bounds physical.capacity.toNat_lt
    rw [UInt64.toNat_add,show (1 : UInt64).toNat = 1 from rfl,Nat.mod_eq_of_lt bound]
  have separation : (sourceOffset+sourceLen).toNat ≤ physical.offset.toNat ∨ (physical.offset+1).toNat ≤ sourceOffset.toNat := by
    rw [returnStop,physicalOffset]
    exact disjoint.symm
  refine ⟨updated,protect,{
    tracker := tracker, borrowFrame := borrowFrame, destination := physical,
    sourceTag := sourceTag, sourceChild := sourceChild, sourceSelected := sourceSelected,
    sourceMaximum := sourceMaximum, sourceOffset := sourceOffset, sourceLen := sourceLen, sourceNode := sourceNode,
    sourceTagged := sourceTaggedPhysical, sourcePresent := sourcePresentPhysical, sourceHidden := sourceHiddenAfter,
    sourceRuntime := runtimePhysical,
    sourcePositive := by rw [physicalEntry,extra]; exact Classical.choice sourceAfter,
    sourceDistinct := by rw [physicalEntry,extra]; exact roots,
    sourceOrder := by intro _ _; rw [physicalEntry,extra]; exact postOrder,
    sourceShort := by rw [physicalEntry,extra]; exact short,
    sourceActivity := by rw [physicalEntry,extra]; exact sourceActive,
    returnTag := input.tracker.global.nextPointerTag, child := child, selected := raw.selected,
    maximum := input.maximum, returnNode := node,
    enabled := rfl, frameTracked := rfl, owned := ownedTags,
    returnTagged := taggedPhysical, returnPresent := presentPhysical, returnSame := same,
    returnEdge := by rw [physicalParent]; exact edge,
    returnHidden := hidden, hiddenFrame := hiddenFrame, runtime := runtimePhysical,
    positive := by rw [physicalEntry,extra,physicalOffset,←selected]; exact Classical.choice positive,
    distinct := by rw [physicalEntry,extra]; exact roots,
    order := by intro _ _; rw [physicalEntry,extra]; exact postOrder,
    short := by rw [physicalEntry,extra]; exact short,
    activity := by rw [physicalEntry,extra,physicalOffset]; exact activity,
    returnLeaf := leaf, childrenDifferent := childrenDifferent, disjoint := separation},rfl,rfl,rfl,rfl,rfl,rfl,oldTag.trans sourceSame,rfl,rfl,rfl,?_,?_,extra⟩
  · rw [extra];exact postOrder
  · rw [extra]
    change written.nodes.size ≤ input.entry.allocation.extra.nodes.size+1
    rw [writtenNodes]
    exact resources.2.2.1

end
end DuplicatePrefix.S02WildcardSameDestinationRejectedProtect
