import duplicate_prefix.GeneralBorrowWildcardSubtreeState

namespace DuplicatePrefix.GeneralBorrowWildcardSubtreeRegion
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective)
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Common root-free region for any finite sequence of extra subtree visits.
Support is child-closed, unexposed, and carries zero counters for this kind. -/
structure Region (tree : BorrowTree) (initial : LocationTree) (kind : AccessKind) (protections : ProtectedTags) where
  support : UniIndex → Prop
  present : ∀ index, support index → ∃ node, tree.nodes.get index = some node
  children : ∀ index node, support index → tree.nodes.get index = some node →
    ∀ child ∈ node.children.toList, support child
  unexposed : ∀ index node, support index → tree.nodes.get index = some node → node.isExposed = false
  zero : ∀ index, support index → GeneralBorrowWildcardRelatednessBounds.count initial.exposedCache index kind = 0
  owned : ∀ index node, support index → tree.nodes.get index = some node →
    GeneralBorrowPermissions.ForeignOwned (effective initial index node) (protections.contains node.tag)

def Owned {tree : BorrowTree} {initial : LocationTree} {kind : AccessKind} {protections : ProtectedTags}
    (region : Region tree initial kind protections) (location : LocationTree) : Prop :=
  ∀ index node, region.support index → tree.nodes.get index = some node →
    GeneralBorrowPermissions.ForeignOwned (effective location index node) (protections.contains node.tag)

/-- Attach any supported current root to the common data. The current owner
and cache frame are preceding visits' derived outputs, not success contracts. -/
def data {tree : BorrowTree} {initial : LocationTree} {kind : AccessKind} {protections : ProtectedTags}
    (region : Region tree initial kind protections) (location : LocationTree)
    (owned : Owned region location) (cache : location.exposedCache = initial.exposedCache)
    (root : UniIndex) (supported : region.support root) :
    GeneralBorrowWildcardSubtreeData.Data tree location root kind protections where
  support := region.support
  root := supported
  present := region.present
  children := region.children
  unexposed := region.unexposed
  zero := by intro index member;rw [cache];exact region.zero index member
  owned := owned

/-- Rebase the same common support on a derived current location. -/
def rebase {tree : BorrowTree} {initial : LocationTree} {kind : AccessKind} {protections : ProtectedTags}
    (region : Region tree initial kind protections) (location : LocationTree)
    (owned : Owned region location) (cache : location.exposedCache = initial.exposedCache) :
    Region tree location kind protections where
  support := region.support
  present := region.present
  children := region.children
  unexposed := region.unexposed
  zero := by intro index member;rw [cache];exact region.zero index member
  owned := owned

end DuplicatePrefix.GeneralBorrowWildcardSubtreeRegion
