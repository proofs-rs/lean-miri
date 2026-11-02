import duplicate_prefix.GeneralBorrowProtectedMutableStage

namespace DuplicatePrefix.GeneralBorrowProtectedMutableLifecycle
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Actual child Write while the fresh strong protector remains registered. -/
def write (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) (global : GlobalState) (allocation : AllocId) :=
  GeneralBorrowProtectedMutableRelease.write
    (GeneralBorrowProtectedMutableStage.child tree parentTag tag offset len global allocation).tree tag offset len
    (GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.protectedTags

/-- Actual protector-end access, before global frame-owned tag removal. -/
def released (tree : BorrowTree) (parentTag tag : BorTag) (offset len : UInt64) (global : GlobalState) (allocation : AllocId) :=
  GeneralBorrowProtectedMutableRelease.release
    (GeneralBorrowProtectedMutableStage.child tree parentTag tag offset len global allocation).tree tag offset len
    (GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.protectedTags

/-- From recurring root State, perform actual fresh Strong registration, root
Read, protected reservation, child Write, source releaseProtector and source
endCall. Every operation completes; root Write ownership is recovered ONLY after
release/endCall, on the created range. No intermediate graph/ownership, success,
release-frame equation or lifetime-restoration contract is supplied. -/
theorem complete (tree : BorrowTree) (root : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (global : GlobalState) (empty : global.protectedTags = {}) (allocation : AllocId) :
    (GeneralBorrowProtectedMutableStage.read tree s.node.tag tag offset len global allocation).status = .Completed ∧
    (GeneralBorrowProtectedMutableStage.child tree s.node.tag tag offset len global allocation).outcome = .ok () ∧
    (write tree s.node.tag tag offset len global allocation).status = .Completed ∧
    (released tree s.node.tag tag offset len global allocation).status = .Released ∧
    ((GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.endCall
      (GeneralBorrowProtectedMutableRelease.registration global allocation tag).2).protectedTags = {} ∧
    OwnedOn (GeneralBorrowRange.LocationOwned (released tree s.node.tag tag offset len global allocation).tree {} root .Write)
      offset (offset+len) (released tree s.node.tag tag offset len global allocation).tree.locations ∧
    (released tree s.node.tag tag offset len global allocation).tree.locations.WellFormed ∧
    (released tree s.node.tag tag offset len global allocation).tree.locations.size = tree.locations.size := by
  obtain ⟨readDone,reservedDone,⟨data⟩⟩ := GeneralBorrowProtectedMutableStage.prepare tree root capacity s offset len nonzero bounds tag fresh global empty allocation
  have final := GeneralBorrowProtectedMutableRelease.write_release_restore (GeneralBorrowProtectedMutableStage.child tree s.node.tag tag offset len global allocation).tree global empty allocation tag data.index root data.node data.rootNode
    data.present data.rootPresent data.parent data.rootless data.unexposed data.lookup data.certificates.depth data.certificates.children data.certificates.covered
    data.roots data.fits offset len nonzero data.well data.bounds data.active data.owned
  refine ⟨readDone,reservedDone,final.1,final.2.1,final.2.2.1,final.2.2.2.1,final.2.2.2.2.1,?_⟩
  exact final.2.2.2.2.2.trans (data.capacity.trans s.capacity.symm)

end DuplicatePrefix.GeneralBorrowProtectedMutableLifecycle
