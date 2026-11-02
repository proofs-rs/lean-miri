import duplicate_prefix.GenericAsMutPtrEntryValidity
import duplicate_prefix.GeneralBorrowTightAncestry

namespace DuplicatePrefix.GenericAsMutPtrEntryPoolData
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 500000

set_option autoImplicit false in
/-- Form the actual FnEntry contract from initial graph/ownership and arbitrary
coherent allocator data. The caller supplies no Slot or strict rank slack;
tight ancestry derives those facts. Per-location ownership remains explicit.
This builder does not generalize the later append-only shared-prefix contract. -/
noncomputable def from_pool (tree : BorrowTree) (protections : ProtectedTags) (parentTag newTag : BorTag)
    (offset len : UInt64) (parent root : UniIndex) (node : TreeNode)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (children : GeneralBorrowGraph.ChildNodes tree)
    (present : tree.nodeAt parent = some node) (roots : tree.roots = #[root])
    (covered : GeneralBorrowGraph.RootsCover tree)
    (tagPresent : tree.indexOfTag parentTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag)
    (protectorFresh : GeneralBorrowProtector.Fresh tree newTag)
    (nodeFits : tree.nodes.data.size ≤ 4294967296)
    (pool : GeneralBorrowFreshAllocatorInvariant.Pool tree.nodes tree.tagMapping.deassigned)
    (aligned : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size = tree.nodes.data.size)
    (fits : tree.tagMapping.deassigned.back? = none → tree.tagMapping.mapping.size ≤ 4294967295)
    (well : tree.locations.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn (GeneralBorrowRange.LocationOwned tree protections parent .Write)
      offset (offset+len) tree.locations) :
    GenericAsMutPtrEntryValidity.Data tree protections parentTag newTag offset len := {
  parent := parent
  root := root
  node := node
  depth := GeneralBorrowTightAncestry.tight tree.nodes depth
  children := children
  parentPresent := present
  roots := roots
  covered := covered
  tagPresent := tagPresent
  tagFresh := tagFresh
  protectorFresh := protectorFresh
  nodeFits := nodeFits
  slot := GeneralBorrowFreshAllocatorInvariant.slot tree
    (GeneralBorrowTightAncestry.tight tree.nodes depth) parent pool aligned fits
    (GeneralBorrowTightAncestry.present_slack tree.nodes depth parent node present)
  well := well
  owned := owned
}
end DuplicatePrefix.GenericAsMutPtrEntryPoolData
