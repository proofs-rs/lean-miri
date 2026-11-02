import duplicate_prefix.GeneralBorrowForestMixedSharedRestoreData
import duplicate_prefix.GeneralBorrowForestMixedSharedLookup
import duplicate_prefix.GeneralBorrowForestMixedTargetRelease
namespace DuplicatePrefix.GeneralBorrowForestMixedSharedRestoredResources
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestMixedSharedArgumentCopy BorrowRangeAccess GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem prepare
    (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState) (id : AllocId)
    (parentTag : BorTag) (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (context : GeneralBorrowForestAccessData.Context tree parent primary extras)
    (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping tracker.global.nextPointerTag)
    (nodeTags : ∀ index node, tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (unheld : tracker.global.protectedTags.get tracker.global.nextPointerTag = none)
    (slot : GeneralBorrowFreshReborrowStages.Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (nonzero : len ≠ 0)
    (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshMetadataChildSlot.index slot) = none) tree.locations)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location tracker.global.protectedTags parent primary extras (GeneralBorrowFreshMixedChild.extend (fun _ => true) parent.toNat)))
      offset (offset+len) tree.locations)
    (target : UniIndex) (targetNode : TreeNode) (targetPresent : tree.nodeAt target = some targetNode)
    (rangePositive : offset.toNat < (offset+len).toNat)
    (exprFree : tracker.global.protectedTags.contains context.anchorNode.tag = false)
    (prefixPath : ∀ location, (source_normal_projection tree location tracker.global.protectedTags).topology.ancestorPath parent.toNat =
      parent.toNat :: (source_normal_projection tree location tracker.global.protectedTags).topology.ancestorPath target.toNat)
    (exprOutside : ∀ location, parent.toNat ∉ (source_normal_projection tree location tracker.global.protectedTags).topology.ancestorPath target.toNat)
    (rootPath : ∀ location, ((source_normal_projection tree location tracker.global.protectedTags).topology.ancestorPath target.toNat).getLast! = primary.toNat)
    (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write offset (offset+len)) :
    let childTree := finalTree tree tracker parentTag offset len
    let held := TypedBorrowSteps.registeredTracker tracker tracker.global.nextPointerTag
    let frame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
    let released := (childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree
    Nonempty (GeneralBorrowForestAccessData.Context released target primary extras) ∧
    released.indexOfTag targetNode.tag = some target ∧ released.nodes.data.size ≤ 4294967296 ∧
    GeneralBorrowFreshReleaseLoop.ActiveOn released target .Write offset (offset+len) ∧
    GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data released location (held.global.endCall frame).protectedTags target primary extras))
      offset (offset+len) released.locations := by
  let labels := GeneralBorrowFreshMixedChild.extend (fun _ => true) parent.toNat
  let childTree := finalTree tree tracker parentTag offset len
  let held := TypedBorrowSteps.registeredTracker tracker tracker.global.nextPointerTag
  let frame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  let released := (childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree
  have data := GeneralBorrowForestMixedSharedReleaseData.prepare tree tracker {} id parentTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits labels nonzero well bounds clean owned
  obtain ⟨nextContext⟩ := data.1
  have nodeData := GeneralBorrowForestMixedSharedNodeData.nodes tree tracker {} id parentTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits labels nonzero well bounds owned target targetNode targetPresent
  obtain ⟨nextNode,nextPresent,nextTag,nextUnexposed⟩ := nodeData.2
  have bounded := GeneralBorrowForestMixedSharedNodeBound.bound tree tracker {} id parentTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits labels nonzero well bounds owned
  have release := GeneralBorrowForestMixedTargetRelease.release tree tracker {} id parentTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits labels nonzero well bounds clean owned target targetActive rangePositive
  have frameEq : released = {childTree with locations := released.locations} := release.2.1
  have targetContext : GeneralBorrowForestAccessData.Context childTree target primary extras :=
    {nextContext with anchorNode := nextNode,anchorPresent := nextPresent}
  have contextReleased : Nonempty (GeneralBorrowForestAccessData.Context released target primary extras) := by
    rw [frameEq]
    exact ⟨{targetContext with anchorPresent := targetContext.anchorPresent,primaryPresent := targetContext.primaryPresent}⟩
  have different : tracker.global.nextPointerTag ≠ targetNode.tag :=
    Ne.symm (GeneralBorrowForestMixedRegister.node_fresh tree tracker.global.nextPointerTag tagFresh nodeTags target targetNode targetPresent)
  have lookup := GeneralBorrowForestMixedSharedLookup.lookup tree tracker {} id parentTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits labels nonzero well bounds owned targetNode.tag different
  have lookupReleased : released.indexOfTag targetNode.tag = some target := by
    rw [frameEq]
    exact lookup.trans (nodeTags target targetNode targetPresent)
  have fitsReleased : released.nodes.data.size ≤ 4294967296 := by rw [frameEq];exact bounded
  obtain ⟨restored,restoreEq,mutable⟩ := GeneralBorrowForestMixedSharedRestoreData.restore tree tracker {} id parentTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits nonzero well bounds clean owned target targetNode targetPresent rangePositive exprFree prefixPath exprOutside rootPath
  have same : restored = released := (congrArg BorrowTree.ProtectorReleaseResult.tree restoreEq).symm
  subst restored
  exact ⟨contextReleased,lookupReleased,fitsReleased,
    GeneralBorrowFreshActiveWithin.active_on released target .Write offset (offset+len) release.2.2.2.1 release.2.2.1,mutable⟩

end DuplicatePrefix.GeneralBorrowForestMixedSharedRestoredResources
