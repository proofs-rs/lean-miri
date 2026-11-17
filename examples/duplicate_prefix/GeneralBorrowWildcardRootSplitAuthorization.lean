import duplicate_prefix.GeneralBorrowWildcardRootAuthorization
import duplicate_prefix.GeneralBorrowFreshRootSupportCutoff
namespace DuplicatePrefix.GeneralBorrowWildcardRootSplitAuthorization
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixResidualSupportAuthorization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- An actual hidden isolated-root insertion turns old wildcard callbacks into
fresh-cutoff callbacks using separate contributor and visited-support bounds.
Newer hidden nodes outside that support impose no tag-order requirement. -/
theorem fresh (tree : BorrowTree) (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (index : UniIndex) (newNode : TreeNode) (vacant : tree.nodes.get index = none)
    (hidden : newNode.isExposed = false) (parentless : newNode.parent = none)
    (size : tree.nodes.size ≤ (tree.nodes.insert index newNode).size)
    (maximum : BorTag)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound tree maximum)
    (before after : LocationTree) (protections : ProtectedTags)
    (slots : ∀ query node,tree.nodes.get query = some node → after.perms.get query = before.perms.get query)
    (root : UniIndex) (position : Nat) (kind : AccessKind) (support : UniIndex → Prop)
    (bounded : GeneralBorrowFreshRootSupportCutoff.SupportBound tree maximum support)
    (old : Authorization tree before protections root position none kind support) :
    Authorization {tree with nodes := tree.nodes.insert index newNode} after protections root position (some maximum) kind support := by
  have next := GeneralBorrowWildcardRootAuthorization.insert tree depth index newNode vacant hidden parentless size
    before after protections slots root position none kind support old
  apply (GeneralBorrowFreshRootSupportCutoff.authorization_iff _ after protections maximum
    (GeneralBorrowFreshRootSupportCutoff.exposed_insert_hidden tree maximum exposed index newNode hidden)
    root position kind support ?_).mp next
  intro query node included present
  have different : query ≠ index := by
    intro same
    obtain ⟨previous,found⟩ := old.present query included
    rw [same,vacant] at found
    contradiction
  change (tree.nodes.insert index newNode).get query = some node at present
  rw [GeneralBorrowFreshLocation.get_other _ index query newNode different] at present
  exact bounded query node included present
end DuplicatePrefix.GeneralBorrowWildcardRootSplitAuthorization
