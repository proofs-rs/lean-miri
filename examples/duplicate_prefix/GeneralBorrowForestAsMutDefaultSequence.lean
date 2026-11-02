import duplicate_prefix.GeneralBorrowForestDefault
namespace DuplicatePrefix.GeneralBorrowForestAsMutDefaultSequence
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
  primary : UniIndex
  extras : List UniIndex
  context : GeneralBorrowForestAccessData.Context tree parent primary extras
  covered : GeneralBorrowGraph.RootsCover tree
  parentTagPresent : tree.indexOfTag parentTag = some parent
  tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag
  nodeFits : tree.nodes.data.size ≤ 4294967296
  slot : Slot tree context.depth parent
  nonzero : len ≠ 0
  well : tree.locations.WellFormed
  bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat

def index {tree : BorrowTree} {newTag : BorTag} {parent : UniIndex} {offset len : UInt64}
    (data : Data tree newTag parent offset len) : UniIndex := GeneralBorrowFreshMetadataChildDefaultSlot.index data.slot

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
    (owned : OwnedOn
      (fun location => Nonempty (GeneralBorrowForestMutableAccess.Data tree location protections parent data.primary data.extras))
      offset (offset+len) tree.locations) :
    (read data protections).status = .Completed ∧ (child data protections).outcome = .ok () := by
  have result := GeneralBorrowForestDefault.run tree protections data.parentTag newTag parent data.primary data.extras offset len
    .VisitChildrenOfAccessed data.context data.covered data.parentTagPresent data.tagFresh data.slot data.nodeFits data.nonzero data.well data.bounds owned
  exact ⟨result.1,result.2.1⟩
end DuplicatePrefix.GeneralBorrowForestAsMutDefaultSequence
