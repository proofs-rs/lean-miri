import duplicate_prefix.GeneralBorrowForestSharedTargetActivity
import duplicate_prefix.GeneralBorrowForestMixedReleaseWithin
import duplicate_prefix.GeneralBorrowForestMixedSharedNodeBound
namespace DuplicatePrefix.GeneralBorrowForestMixedTargetRelease
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestMixedSharedArgumentCopy
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
theorem release
    (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState) (id : AllocId)
    (parentTag : BorTag) (parent primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (context : GeneralBorrowForestAccessData.Context tree parent primary extras)
    (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping tracker.global.nextPointerTag)
    (nodeTags : ∀ index node, tree.nodeAt index = some node → tree.indexOfTag node.tag = some index)
    (unheld : tracker.global.protectedTags.get tracker.global.nextPointerTag = none)
    (slot : GeneralBorrowFreshReborrowStages.Slot tree context.depth parent)
    (fits : tree.nodes.data.size ≤ 4294967296) (writable : Nat → Bool) (nonzero : len ≠ 0)
    (well : tree.locations.WellFormed) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree =>
      location.perms.get (GeneralBorrowFreshMetadataChildSlot.index slot) = none) tree.locations)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMixedAccess.Data tree location tracker.global.protectedTags parent primary extras writable))
      offset (offset+len) tree.locations)
    (target : UniIndex) (targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin tree target .Write offset (offset+len))
    (positive : offset.toNat < (offset+len).toNat) :
    let childTree := finalTree tree tracker parentTag offset len
    let held := (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags
    let result := childTree.releaseProtector tracker.global.nextPointerTag held
    result.status = .Released ∧
      result.tree = {childTree with locations := result.tree.locations} ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin result.tree target .Write offset (offset+len) ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size = childTree.locations.size := by
  have data := GeneralBorrowForestMixedSharedReleaseData.prepare tree tracker borrowFrame id parentTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits writable nonzero well bounds clean owned
  obtain ⟨nextContext⟩ := data.1
  have bound := GeneralBorrowForestMixedSharedNodeBound.bound tree tracker borrowFrame id parentTag parent primary extras offset len
    context covered tagPresent tagFresh nodeTags unheld slot fits writable nonzero well bounds owned
  have protectorFresh : GeneralBorrowProtector.Fresh tree tracker.global.nextPointerTag := by
    intro row member
    have present := (GeneralBorrowFreshReuseProtection.entries_get tree.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
    exact GeneralBorrowForestMixedRegister.node_fresh tree tracker.global.nextPointerTag tagFresh nodeTags row.1 row.2 present
  have targetWithin := GeneralBorrowForestSharedTargetActivity.preserves_target tree tracker.global.protectedTags true
    parentTag tracker.global.nextPointerTag parent primary extras context covered tagPresent tagFresh protectorFresh fits slot
    offset len nonzero well bounds writable owned target offset (offset+len) (Nat.le_refl _) (Nat.le_refl _) targetActive
  have childWithin := GeneralBorrowForestSharedWithinStages.borrow tree tracker.global.protectedTags true
    parentTag tracker.global.nextPointerTag parent primary extras context covered tagPresent tagFresh protectorFresh fits slot
    offset len nonzero well bounds writable owned clean
  have childActive : GeneralBorrowFreshActiveWithin.ActiveWithin (finalTree tree tracker parentTag offset len)
      (GeneralBorrowFreshMetadataChildSlot.index slot) .Read offset (offset+len) := by
    cases slot <;> simpa only [finalTree,GeneralBorrowFreshSharedWithinStages.slot_index,GeneralBorrowFreshMetadataChildSlot.index,
      GeneralBorrowFreshAnchor.sharedState,NestedConstruction.frozenRead,TypedBorrowSteps.registeredGlobal,ite_true] using childWithin.2.2.2
  have targetActiveAfter : GeneralBorrowFreshActiveWithin.ActiveWithin (finalTree tree tracker parentTag offset len) target .Write offset (offset+len) := by
    simpa only [finalTree,GeneralBorrowFreshAnchor.sharedState,NestedConstruction.frozenRead,TypedBorrowSteps.registeredGlobal,ite_true] using targetWithin
  have released := GeneralBorrowForestMixedReleaseWithin.release (finalTree tree tracker parentTag offset len)
    (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags tracker.global.nextPointerTag
    (GeneralBorrowFreshMetadataChildSlot.index slot) primary extras
    (GeneralBorrowFreshMixedChild.extend writable (GeneralBorrowFreshMetadataChildSlot.index slot).toNat)
    offset (offset+len) positive bound nextContext data.2.2.1 childActive target data.2.2.2.1 targetActiveAfter data.2.1
  exact ⟨released.1,released.2.1,released.2.2.2.1,released.2.2.2.2.1,released.2.2.2.2.2⟩
end DuplicatePrefix.GeneralBorrowForestMixedTargetRelease
