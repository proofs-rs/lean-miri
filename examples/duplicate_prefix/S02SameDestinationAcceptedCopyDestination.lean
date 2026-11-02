import duplicate_prefix.S02SameDestinationAcceptedMutableSuffix
import duplicate_prefix.S02SameDestinationAcceptedCopyRanges
import duplicate_prefix.S02SameDestinationAcceptedCopyMetadata
import duplicate_prefix.S02SameDestinationAcceptedSourceLedger
namespace DuplicatePrefix.S02SameDestinationAcceptedCopyDestination
open Miri Miri.Memory Miri.ABI Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Current destination authorization and leaf activity after the exact mutable
suffix and actual adjacent copy, from the original disjoint return leaf. -/
theorem current (original : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (base offset len count : UInt64) (tracker : MachineHooks.BorrowState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts original.allocation.extra tracker.global)
    (raw : GeneralBorrowRawDefault.Input original.allocation.extra tracker.global)
    (headroom : original.allocation.extra.nodes.size+2 < 65536)
    (tagsRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (ordered : GeneralBorrowWildcardParentTagOrder.ParentTagOrder original.allocation.extra)
    (packet : GeneralBorrowRawAsMutToCopy.Input) (result : Allocation Provenance BorrowTree)
    (connection : S02SameDestinationAcceptedSourceLedger.Connection original machine id base offset len count tracker raw packet result)
    (target selected : UniIndex) (maximum : Option BorTag) (lower width : UInt64)
    (outside : raw.offset.toNat+raw.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ raw.offset.toNat)
    (positive : DuplicatePrefixBorrowAuthorization.Positive original.allocation.extra tracker.global.protectedTags (some target) (some selected) maximum lower width)
    (node : TreeNode) (present : original.allocation.extra.nodeAt target = some node)
    (leaf : node.children = #[]) (hidden : node.isExposed = false) (different : target ≠ raw.parent)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin original.allocation.extra target .Write lower (lower+width)) :
    Nonempty (DuplicatePrefixBorrowAuthorization.Positive result.extra (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags (some target) (some selected) maximum lower width) ∧
    GeneralBorrowFreshActiveWithin.ActiveWithin result.extra target .Write lower (lower+width) ∧
    (∃ next, result.extra.nodeAt target = some next ∧ next.tag = node.tag ∧ next.parent = node.parent ∧ next.children = #[] ∧ next.isExposed = false) ∧
    GeneralBorrowWildcardParentTagOrder.ParentTagOrder result.extra ∧
    (∀ tag query, original.allocation.extra.indexOfTag tag = some query → result.extra.indexOfTag tag = some query) ∧
    result.extra.locations.size = original.allocation.extra.locations.size := by
  let tree := original.allocation.extra
  let advanced := ReferenceBorrowDriver.allocatedTracker tracker raw.tagRoom
  let expr := (GeneralBorrowRawDefaultExpression.child tree tracker.global.protectedTags raw.parentTag tracker.global.nextPointerTag raw.offset raw.len .VisitChildrenOfAccessed).tree
  obtain ⟨secondFresh,resources⟩ := connection.resources
  obtain ⟨next,nextTag,nextOffset,nextLen,⟨suffixPositive⟩,suffixActivity,last,lastPresent,lastTag,lastParent,lastLeaf,lastHidden⟩ :=
    S02SameDestinationAcceptedMutableSuffix.destination tree tracker packet.id runtime raw headroom tagsRoom target selected maximum lower width outside positive node present leaf hidden different activity
  simp only [nextTag,nextOffset,nextLen] at suffixPositive suffixActivity lastPresent
  let released := (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
  have releasedPositive : DuplicatePrefixBorrowAuthorization.Positive released (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags (some target) (some selected) maximum lower width := by
    unfold released GeneralBorrowRawAsMutToCopy.held
    rw [resources.treeEq,resources.tagEq,resources.trackerEq]
    exact suffixPositive
  have releasedActive : GeneralBorrowFreshActiveWithin.ActiveWithin released target .Write lower (lower+width) := by
    unfold released
    rw [resources.treeEq,resources.tagEq,resources.trackerEq]
    exact suffixActivity
  have releasedPresent : released.nodeAt target = some last := by
    unfold released
    rw [resources.treeEq,resources.tagEq,resources.trackerEq]
    exact lastPresent
  have releaseFrame := GeneralBorrowStructuralReleaseGeometryFrame.release packet.entry.allocation.extra packet.tracker.global.protectedTags packet.tag
  have releaseNodes := congrArg BorrowTree.nodes releaseFrame
  change released.nodes = packet.entry.allocation.extra.nodes at releaseNodes
  have targetPresent : packet.entry.allocation.extra.nodeAt target = some last := by
    change released.nodes.get target = some last at releasedPresent
    change packet.entry.allocation.extra.nodes.get target = some last
    rw [←releaseNodes];exact releasedPresent
  have differentPacket : target ≠ packet.anchor := by
    intro same
    have found : packet.entry.allocation.extra.nodeAt packet.anchor = some last := by simpa only [same] using targetPresent
    have equal : last = packet.node := Option.some.inj (found.symm.trans packet.nodePresent)
    have tags : node.tag = packet.tag := lastTag.symm.trans ((congrArg TreeNode.tag equal).trans packet.sameTag)
    have below := GeneralBorrowParentTagInvariant.parent_below_fresh tree tracker.global runtime target node present
    have firstBound := UInt64.lt_iff_toNat_lt.mp below
    have allocated : packet.tag.value.toNat = tracker.global.nextPointerTag.value.toNat+1 := by
      rw [resources.tagEq]
      exact GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag raw.tagRoom
    have impossible := congrArg (fun tag : BorTag => tag.value.toNat) tags
    omega
  obtain ⟨copyInput,anchorEq,_selectedEq,_maximumEq⟩ := GeneralBorrowRawAsMutCopyResources.copy_input packet
  have copiedOutside : packet.offset.toNat+packet.len.toNat ≤ lower.toNat ∨ (lower+width).toNat ≤ packet.offset.toNat := by
    simpa only [connection.rawOffset,connection.rawLen,connection.metadata.offsetEq,connection.metadata.lenEq] using outside
  have copyFacts := S02SameDestinationAcceptedCopyRanges.destination released (GeneralBorrowRawAsMutToCopy.held packet).global packet.tag
    packet.offset packet.len packet.count copyInput (UInt64.lt_iff_toNat_lt.mp packet.countPositive)
    target selected maximum lower width copiedOutside releasedPositive last releasedPresent lastLeaf lastHidden
    (by rw [anchorEq];exact differentPacket) releasedActive
  obtain ⟨copiedPositive,copiedActive,copiedPresent⟩ := copyFacts
  rw [←connection.tree] at copiedPositive copiedActive copiedPresent
  have currentNodes : result.extra.nodes = packet.entry.allocation.extra.nodes := by
    rw [connection.tree]
    exact GeneralBorrowRawMutableParentRestore.copy_nodes packet
  have currentTags : result.extra.tagMapping = packet.entry.allocation.extra.tagMapping := by
    rw [connection.tree]
    exact S02SameDestinationAcceptedCopyMetadata.copy_tags packet
  obtain ⟨currentOrder,mapped⟩ := S02SameDestinationAcceptedCopyMetadata.current tree tracker id runtime raw headroom tagsRoom ordered packet secondFresh resources result.extra currentNodes currentTags
  obtain ⟨exprRuntime,exprCapacity,_room,next2,next2Tag,_selected2,_maximum2,next2Offset,next2Len⟩ := GeneralBorrowRawDefaultResources.resources tree tracker runtime raw headroom tagsRoom
  have helper := GeneralBorrowRawFnEntryResources.resources expr advanced {} id exprRuntime next2
  have helperCapacity := helper.2.1
  simp only [next2Tag,next2Offset,next2Len] at helperCapacity
  have packetCapacity : packet.entry.allocation.extra.locations.size = tree.locations.size := by
    rw [resources.treeEq]
    exact helperCapacity.trans exprCapacity
  have operations := GeneralBorrowRawCopyInput.accesses _ _ _ _ _ _ copyInput
  have releaseCapacity := (GeneralBorrowStructuralReleaseGeometry.release packet.entry.allocation.extra packet.tracker.global.protectedTags packet.tag packet.runtime.formed.well).2
  have currentCapacity : result.extra.locations.size = tree.locations.size := by
    rw [connection.tree]
    exact operations.2.1.capacity.trans (operations.1.capacity.trans (releaseCapacity.trans packetCapacity))
  exact ⟨copiedPositive,copiedActive,⟨last,copiedPresent,lastTag,lastParent,lastLeaf,lastHidden⟩,currentOrder,mapped,currentCapacity⟩
end
end DuplicatePrefix.S02SameDestinationAcceptedCopyDestination
