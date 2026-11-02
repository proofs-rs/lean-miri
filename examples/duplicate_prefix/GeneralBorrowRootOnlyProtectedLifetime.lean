import duplicate_prefix.GeneralBorrowRootOnlyProtectedRelease
import duplicate_prefix.GeneralBorrowRootOnlyProtectedConstructors
import duplicate_prefix.GeneralBorrowProtectedMutableHistoryStage

namespace DuplicatePrefix.GeneralBorrowRootOnlyProtectedLifetime
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Full actual protected mutable lifetime retains the root-only protocol:
registration, root Read, protected Default reservation, child Write, actual
releaseProtector and matching endCall preserve exact root cache/Unique storage
and the root's exposure flag. No cache or operation-success conclusion is a
premise; registered root Write is not asserted. -/
theorem stage (tree : BorrowTree) (root : UniIndex) (capacity : UInt64) (s : State tree root capacity)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag) (room : tree.nodes.size+5 ≤ 4294967295)
    (global : GlobalState) (empty : global.protectedTags = {}) (allocation : AllocId)
    (cache : ExposedCache) (only : RootOnly tree root) (initial : Every (LocationInvariant cache root) tree.locations) :
    let after := (GeneralBorrowProtectedMutableLifecycle.released tree s.node.tag tag offset len global allocation).tree
    RootOnly after root ∧ Every (LocationInvariant cache root) after.locations ∧
      (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed := by
  dsimp only
  let protections := (GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.protectedTags
  have singleton : protections = ({} : ProtectedTags).insert tag .StrongProtector := by
    simp [protections,GeneralBorrowProtectedMutableRelease.registration,GlobalState.addProtector,empty]
  let entry := GeneralBorrowPartitionEntryData.data tree root capacity s tag fresh
  have allRoot := GeneralBorrowProtector.range_owned tree {} tag .StrongProtector entry.protectorFresh root .Write s.owned
  rw [←singleton] at allRoot
  have readOwned : Every (GeneralBorrowRange.LocationOwned tree protections root .Read) tree.locations := by
    intro position valid
    obtain ⟨forest,owner⟩ := allRoot position valid
    exact ⟨forest,GeneralBorrowRangePreserves.owned_for_access _ root.toNat .Read .Write (by intro impossible;cases impossible) owner⟩
  have request : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat := by rw [s.capacity];exact bounds
  have readCache := GeneralBorrowRootOnlyRangeCache.ranged tree s.node.tag root s.node (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
    cache entry.nodeFits entry.depth entry.children s.star.present s.roots entry.covered (s.allocator.nodeTags root s.node s.star.present)
    s.well only readOwned initial request
  let accessed := (GeneralBorrowProtectedMutableStage.read tree s.node.tag tag offset len global allocation).tree
  have firstFrame := GeneralBorrowFreshReadFrame.frame tree (.concrete s.node.tag) (Size.ofBytes offset) (Size.ofBytes len) .Read protections .VisitChildrenOfAccessed
  have readNodes : accessed.nodes = tree.nodes := by simpa only [accessed,GeneralBorrowProtectedMutableStage.read,protections] using congrArg BorrowTree.nodes firstFrame
  have readOnly : RootOnly accessed root := by intro index node found flag;rw [readNodes] at found;exact only index node found flag
  have readInvariant : Every (LocationInvariant cache root) accessed.locations := readCache.2
  have readFlag : (accessed.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed := by rw [readNodes]
  have readEq : GeneralBorrowProtectedMutableStage.read tree s.node.tag tag offset len global allocation =
      GeneralBorrowProtectedRootRead.operation tree s.node.tag offset len tag := by
    simp only [GeneralBorrowProtectedMutableStage.read,GeneralBorrowProtectedRootRead.operation,BorrowTree.performNormalAccessRange]
    rw [show (GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.protectedTags = ({} : ProtectedTags).insert tag .StrongProtector from singleton]
  have readResult := GeneralBorrowProtectedRootRead.read tree root capacity s offset len tag fresh bounds
  rw [←readEq] at readResult
  obtain ⟨⟨afterRead,readTag⟩⟩ := readResult.2.1
  have freshRead : GeneralBorrowTagMap.Fresh accessed.tagMapping tag := by rw [readResult.2.2.2];exact fresh
  have roomRead : accessed.nodes.size+5 ≤ 4294967295 := by rw [readResult.2.2.1];exact room
  have constructed := GeneralBorrowRootOnlyProtectedConstructors.reserve accessed root capacity afterRead offset len nonzero bounds tag freshRead roomRead cache readOnly readInvariant
  have constructorFlag := GeneralBorrowRootOnlyProtectedConstructors.Flags.reserve accessed root capacity afterRead offset len nonzero bounds tag freshRead roomRead
  have prepared := GeneralBorrowProtectedConstructorState.prepare accessed root capacity afterRead offset len nonzero bounds tag freshRead roomRead
  have treeEq : GeneralBorrowProtectedConstructorState.reserved accessed afterRead.node.tag tag offset len =
      (GeneralBorrowProtectedMutableStage.child tree s.node.tag tag offset len global allocation).tree := by rw [readTag];rfl
  have operationEq : GeneralBorrowPartitionProtectedDefault.operation accessed afterRead.node.tag tag offset len =
      GeneralBorrowProtectedMutableStage.child tree s.node.tag tag offset len global allocation := by rw [readTag];rfl
  rw [operationEq] at constructed constructorFlag
  rw [treeEq] at prepared
  obtain ⟨reservedOK,before,index,node,rootTag,lookup,present,tagged,parent,typed⟩ := prepared
  obtain ⟨readDone,childDone,⟨data⟩⟩ := GeneralBorrowProtectedMutableStage.prepare tree root capacity s offset len nonzero bounds tag fresh global empty allocation
  have sameIndex : index = data.index := Option.some.inj (lookup.symm.trans data.lookup)
  subst index
  have finished := GeneralBorrowRootOnlyProtectedRelease.frame (GeneralBorrowProtectedMutableStage.child tree s.node.tag tag offset len global allocation).tree root data.index capacity
    before data.node data.present data.parent data.unexposed tag data.lookup typed offset len nonzero bounds data.active global empty allocation cache constructed.1 constructed.2
  exact ⟨finished.1,finished.2.1,finished.2.2.trans (constructorFlag.trans readFlag)⟩
end
end DuplicatePrefix.GeneralBorrowRootOnlyProtectedLifetime
