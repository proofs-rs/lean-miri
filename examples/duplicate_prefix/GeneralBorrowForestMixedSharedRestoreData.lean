import duplicate_prefix.GeneralBorrowForestMixedSharedNodeBound
import duplicate_prefix.GeneralBorrowForestMixedSharedNodeData
import duplicate_prefix.GeneralBorrowForestSharedPrefixPaths
import duplicate_prefix.GeneralBorrowForestMixedRestore
import duplicate_prefix.GeneralBorrowForestMixedReleaseFrame
namespace DuplicatePrefix.GeneralBorrowForestMixedSharedRestoreData
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestMixedSharedArgumentCopy BorrowRangeAccess GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem restore
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
    (rootPath : ∀ location, ((source_normal_projection tree location tracker.global.protectedTags).topology.ancestorPath target.toNat).getLast! = primary.toNat) :
    let childTree := finalTree tree tracker parentTag offset len
    let held := TypedBorrowSteps.registeredTracker tracker tracker.global.nextPointerTag
    let frame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
    ∃ released, childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags = ⟨released,.Released⟩ ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data released location (held.global.endCall frame).protectedTags target primary extras))
        offset (offset+len) released.locations := by
  let labels := GeneralBorrowFreshMixedChild.extend (fun _ => true) parent.toNat
  let child := GeneralBorrowFreshMetadataChildSlot.index slot
  let childTree := finalTree tree tracker parentTag offset len
  let held := TypedBorrowSteps.registeredTracker tracker tracker.global.nextPointerTag
  let frame := ({} : FrameState).addProtector id tracker.global.nextPointerTag
  have data := GeneralBorrowForestMixedSharedReleaseData.prepare tree tracker {} id parentTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits labels nonzero well bounds clean owned
  obtain ⟨nextContext⟩ := data.1
  have bound := GeneralBorrowForestMixedSharedNodeBound.bound tree tracker {} id parentTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits labels nonzero well bounds owned
  have nodeData := GeneralBorrowForestMixedSharedNodeData.nodes tree tracker {} id parentTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits labels nonzero well bounds owned
  obtain ⟨⟨childNode,childPresent,childTag,childUnexposed⟩,targetNew,targetNewPresent,targetTag,targetUnexposed⟩ := nodeData target targetNode targetPresent
  obtain ⟨_,exprNew,exprNewPresent,exprTag,exprUnexposed⟩ := nodeData parent context.anchorNode context.anchorPresent
  have attached := GeneralBorrowForestMixedSharedAttach.attach tree tracker {} id parentTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits labels nonzero well bounds owned
  have paths (location : LocationTree) := GeneralBorrowForestSharedPrefixPaths.extend
    (source_normal_projection tree location tracker.global.protectedTags).topology
    (source_normal_projection childTree location tracker.global.protectedTags).topology
    target.toNat parent.toNat child.toNat (attached location location tracker.global.protectedTags)
    (by unfold_general_projection;unfold_general_topology;simp only [Array.size_map];exact GeneralBorrowNodeUpdate.lookup_valid tree.nodes target targetNode targetPresent) (prefixPath location) (exprOutside location)
  have exprDifferent : context.anchorNode.tag ≠ tracker.global.nextPointerTag :=
    GeneralBorrowForestMixedRegister.node_fresh tree tracker.global.nextPointerTag tagFresh nodeTags parent context.anchorNode context.anchorPresent
  have exprUnheld : held.global.protectedTags.contains exprNew.tag = false := by
    rw [exprTag]
    change (tracker.global.protectedTags.insert tracker.global.nextPointerTag .StrongProtector).contains context.anchorNode.tag = false
    rw [ProtectorInsertion.contains_other tracker.global.protectedTags tracker.global.nextPointerTag context.anchorNode.tag .StrongProtector exprDifferent]
    exact exprFree
  have topology (location : LocationTree) :
      (source_normal_projection childTree location held.global.protectedTags).topology =
      (source_normal_projection childTree location tracker.global.protectedTags).topology :=
    GeneralBorrowFreshSharedStagePaths.topology_any _ _ _ _ _
  have restoration := GeneralBorrowFreshSharedPrefix.restore_data childTree held.global frame target parent child
    targetNew exprNew childNode targetNewPresent exprNewPresent childPresent id
    (by rw [childTag];simp [frame,FrameState.addProtector]) exprUnheld
    (fun location => by rw [topology];exact (paths location).1)
    (fun location => by rw [topology];exact (paths location).2.1)
    (fun location => by rw [topology];exact (paths location).2.2.1)
  have released := GeneralBorrowForestMixedReleaseFrame.release childTree held.global.protectedTags tracker.global.nextPointerTag
    child primary extras (GeneralBorrowFreshMixedChild.extend labels child.toNat) offset (offset+len) rangePositive bound nextContext
    data.2.2.1 data.2.2.2.2 data.2.1
  let result := childTree.releaseProtector tracker.global.nextPointerTag held.global.protectedTags
  have complete : result = ⟨result.tree,.Released⟩ := by
    cases eqn : result with
    | mk tree status => have done := released.1;change result.status = .Released at done;rw [eqn] at done;cases done;rfl
  have restoreReleased : GeneralBorrowFreshLifetimeRestore.RestoreTo result.tree held.global.protectedTags
      (held.global.endCall frame).protectedTags child target (GeneralBorrowFreshSharedPrefix.labels parent child) := by
    rw [released.2.1]
    exact GeneralBorrowFreshLifetimeRestore.restore_map childTree result.tree.locations _ _ child target _ restoration
  have releasedPath (location : LocationTree) :
      ((source_normal_projection result.tree location held.global.protectedTags).topology.ancestorPath target.toNat).getLast! = primary.toNat := by
    rw [released.2.1]
    change ((source_normal_projection childTree location held.global.protectedTags).topology.ancestorPath target.toNat).getLast! = _
    rw [topology,(paths location).2.2.2]
    exact rootPath location
  refine ⟨result.tree,complete,?_⟩
  intro position valid positive start stop
  obtain ⟨localData⟩ := released.2.2 position valid positive start stop
  apply Nonempty.intro
  apply GeneralBorrowForestMixedRestore.restore result.tree _ held.global.protectedTags (held.global.endCall frame).protectedTags
    (GeneralBorrowRelease.end_call_weakens held.global frame) child target primary extras (GeneralBorrowFreshSharedPrefix.labels parent child)
    restoreReleased _ localData
  exact releasedPath _
end DuplicatePrefix.GeneralBorrowForestMixedSharedRestoreData
