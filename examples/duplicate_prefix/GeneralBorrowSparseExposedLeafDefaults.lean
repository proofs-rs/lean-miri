import duplicate_prefix.GeneralBorrowSparseExposedLeafHistory
namespace DuplicatePrefix.GeneralBorrowSparseExposedLeafDefaults
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A real Default constructor's lazy outside reservation is possible and
locally writable even before any explicit per-byte row is materialized. -/
theorem vacant_reserved (location : LocationTree) (index : UniIndex) (node : TreeNode) (held : Bool)
    (absent : location.perms.get index=none) (permission : node.defaultInitialPermission=.ReservedFrz false) :
    GeneralBorrowExposedConditionalWritePermissions.Compatible
      (GeneralBorrowWildcardVirtualLeaf.effective location index node) .LocalAccess held := by
  simp [GeneralBorrowWildcardVirtualLeaf.effective,absent,TreeNode.defaultLocationState,permission,
    GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]

/-- Active stored Unique is a different source case from an impossible lazy
Unique default; the sparse invariant accepts the former for either held bit. -/
theorem stored_unique (location : LocationTree) (index : UniIndex) (node : TreeNode) (held : Bool)
    (present : location.perms.get index=some GeneralBorrowWildcardLeaf.unique) :
    GeneralBorrowExposedConditionalWritePermissions.Compatible
      (GeneralBorrowWildcardVirtualLeaf.effective location index node) .LocalAccess held := by
  simp [GeneralBorrowWildcardVirtualLeaf.effective,present,GeneralBorrowWildcardLeaf.unique,
    GeneralBorrowExposedConditionalWritePermissions.Compatible,LocationState.possible,Permission.isUnique]

/-- Source default-state semantics excludes absent Unique. Treating every
vacant row as an active Unique owner would silently admit impossible states. -/
theorem vacant_unique_impossible (location : LocationTree) (index : UniIndex) (node : TreeNode)
    (absent : location.perms.get index=none) (permission : node.defaultInitialPermission=.Unique) :
    (GeneralBorrowWildcardVirtualLeaf.effective location index node).possible=false := by
  simp [GeneralBorrowWildcardVirtualLeaf.effective,absent,TreeNode.defaultLocationState,permission,LocationState.possible,Permission.isUnique]
end DuplicatePrefix.GeneralBorrowSparseExposedLeafDefaults
