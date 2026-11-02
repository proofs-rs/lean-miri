import duplicate_prefix.GeneralBorrowForestEntrySharedInput
import duplicate_prefix.GeneralBorrowForestMixedSharedResources
namespace DuplicatePrefix.GeneralBorrowForestRejectedTreeData
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
noncomputable section

def tree (before : BorrowTree) (tracker : MachineHooks.BorrowState) (rootTag : BorTag) (offset len : UInt64) :=
  (GeneralBorrowForestMixedShared.child before tracker.global.protectedTags rootTag tracker.global.nextPointerTag false offset len .VisitChildrenOfAccessed).tree

set_option autoImplicit false in
structure Data (before : BorrowTree) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (rootTag : BorTag) (target primary : UniIndex) (extras : List UniIndex) (offset len : UInt64)
    (first : GeneralBorrowForestEntrySharedInput.First before tracker.global.protectedTags rootTag tracker.global.nextPointerTag
      (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag target primary extras offset len) where
  next : GeneralBorrowForestMixedSharedResources.Next (tree before tracker rootTag offset len) tracker.global.protectedTags
    tracker.global.nextPointerTag (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag
    (GeneralBorrowFreshMetadataChildSlot.index first.slot) primary extras offset len
    (GeneralBorrowFreshMixedChild.extend (fun _ => true) (GeneralBorrowFreshMetadataChildSlot.index first.slot).toNat)
  targetNode : TreeNode
  targetPresent : (tree before tracker rootTag offset len).nodeAt target = some targetNode
  targetTag : targetNode.tag = rootTag
  exprFree : tracker.global.protectedTags.contains next.context.anchorNode.tag = false
  prefixPath : ∀ location, (source_normal_projection (tree before tracker rootTag offset len) location tracker.global.protectedTags).topology.ancestorPath
      (GeneralBorrowFreshMetadataChildSlot.index first.slot).toNat =
    (GeneralBorrowFreshMetadataChildSlot.index first.slot).toNat ::
      (source_normal_projection (tree before tracker rootTag offset len) location tracker.global.protectedTags).topology.ancestorPath target.toNat
  exprOutside : ∀ location, (GeneralBorrowFreshMetadataChildSlot.index first.slot).toNat ∉
    (source_normal_projection (tree before tracker rootTag offset len) location tracker.global.protectedTags).topology.ancestorPath target.toNat
  rootPath : ∀ location, ((source_normal_projection (tree before tracker rootTag offset len) location tracker.global.protectedTags).topology.ancestorPath target.toNat).getLast! = primary.toNat
  targetActive : GeneralBorrowFreshActiveWithin.ActiveWithin (tree before tracker rootTag offset len) target .Write offset (offset+len)
  capacity : (tree before tracker rootTag offset len).locations.size = before.locations.size
end
end DuplicatePrefix.GeneralBorrowForestRejectedTreeData
