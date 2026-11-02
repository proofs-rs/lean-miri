import duplicate_prefix.GeneralBorrowFreshDefaultActivity
namespace DuplicatePrefix.GeneralBorrowFreshDefaultSequence
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins
open DuplicatePrefix.GeneralBorrowFreshReborrowStages
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- Caller metadata for one real unprotected mutable expression. The owned slice is supplied
separately, so the surrounding runtime consumes only proved constructor results. -/
structure Data (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64) where
  parentTag : BorTag
  root : UniIndex
  parentNode : TreeNode
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  children : GeneralBorrowGraph.ChildNodes tree
  parentPresent : tree.nodeAt parent = some parentNode
  roots : tree.roots = #[root]
  covered : GeneralBorrowGraph.RootsCover tree
  parentTagPresent : tree.indexOfTag parentTag = some parent
  tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag
  nodeFits : tree.nodes.data.size ≤ 4294967296
  slot : Slot tree depth parent
  nonzero : len ≠ 0
  well : tree.locations.WellFormed
  bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat
  clean : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshDefaultStages.slot_index slot) = none) tree.locations

def index {tree : BorrowTree} {newTag : BorTag} {parent : UniIndex} {offset len : UInt64}
    (data : Data tree newTag parent offset len) : UniIndex := GeneralBorrowFreshDefaultStages.slot_index data.slot

def read {tree : BorrowTree} {newTag : BorTag} {parent : UniIndex} {offset len : UInt64}
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) :=
  tree.performBorrowAccessRange (.concrete data.parentTag) (Size.ofBytes offset) (Size.ofBytes len)
    .Read protections .VisitChildrenOfAccessed

def child {tree : BorrowTree} {newTag : BorTag} {parent : UniIndex} {offset len : UInt64}
    (data : Data tree newTag parent offset len) (protections : ProtectedTags) :=
  (read data protections).tree.newChild (Size.ofBytes offset) (.concrete data.parentTag) newTag
    (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false

theorem run (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write) offset (offset+len) tree.locations) :
    (read data protections).status = .Completed ∧ (child data protections).outcome = .ok () ∧
      OwnedOn (GeneralBorrowRange.LocationOwned (child data protections).tree protections (index data) .Write)
        offset (offset+len) (child data protections).tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (child data protections).tree (index data) .Write offset (offset+len) := by
  exact GeneralBorrowFreshDefaultStages.borrow tree protections data.parentTag newTag parent data.root data.parentNode
    data.depth data.children data.parentPresent data.roots data.covered data.parentTagPresent data.tagFresh
    data.nodeFits data.slot offset len data.nonzero data.well data.bounds owned data.clean

theorem run_active (tree : BorrowTree) (newTag : BorTag) (parent : UniIndex) (offset len : UInt64)
    (data : Data tree newTag parent offset len) (protections : ProtectedTags)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write) offset (offset+len) tree.locations)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree parent .Write offset (offset+len)) :
    (read data protections).status = .Completed ∧ (child data protections).outcome = .ok () ∧
      OwnedOn (GeneralBorrowRange.LocationOwned (child data protections).tree protections (index data) .Write)
        offset (offset+len) (child data protections).tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (child data protections).tree (index data) .Write offset (offset+len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin (child data protections).tree parent .Write offset (offset+len) := by
  exact GeneralBorrowFreshDefaultActivity.borrow tree protections data.parentTag newTag parent data.root data.parentNode
    data.depth data.children data.parentPresent data.roots data.covered data.parentTagPresent data.tagFresh
    data.nodeFits data.slot offset len data.nonzero data.well data.bounds owned data.clean
    parent offset (offset+len) (Nat.le_refl _) (Nat.le_refl _) active
end DuplicatePrefix.GeneralBorrowFreshDefaultSequence
