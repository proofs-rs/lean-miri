import duplicate_prefix.GeneralBorrowParentRestoreNormal
import duplicate_prefix.GeneralBorrowSharedNormalRelations
namespace DuplicatePrefix.GeneralBorrowParentRestoreSupport
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Protector removal retains every other tag lookup exactly. -/
theorem contains_other (tags : ProtectedTags) (removed query : BorTag) (different : query ≠ removed) :
    (tags.remove removed).contains query = tags.contains query := by
  unfold ProtectedTags.contains ProtectedTags.get ProtectedTags.remove
  rw [Array.find?_filter]
  have predicates : (fun row : BorTag × ProtectorKind => decide (row.1 != removed ∧ row.1 == query)) =
      (fun row => row.1 == query) := by
    funext row
    by_cases same : row.1 = query <;> simp [same,different]
  rw [predicates]

/-- Current child Both derives the exact local support stability needed by
protector-release accounting, including arbitrary accessed and SIFA fields. -/
theorem child_level (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags)
    (child : UniIndex) (node : TreeNode) (present : tree.nodeAt child = some node)
    (held : tags.contains node.tag = true)
    (old : DuplicatePrefixBorrowAuthorization.Normal tree location tags child) :
    ((location.perms.get child).getD node.defaultLocationState).permission.strongestAllowedLocalAccess false =
      ((location.perms.get child).getD node.defaultLocationState).permission.strongestAllowedLocalAccess true := by
  have valid := GeneralBorrowNodeUpdate.lookup_valid tree.nodes child node present
  obtain ⟨state,stored,compatible⟩ := old.permissions .Write child.toNat old.component.anchor valid
  rw [GeneralBorrowSharedNormalRelations.child_self,
    GeneralBorrowNormalPermissionMetadata.held tree location tags child node present,held] at compatible
  have exactState := projection_state tree location tags child.toNat child node
    (GeneralBorrowProjection.index_self child) rfl present
  rw [stored] at exactState
  have equal := Option.some.inj exactState
  rw [←equal]
  exact GeneralBorrowParentRestoreScalar.strongest_stable state compatible

/-- Node/tag coherence makes the changed protector unique to the child.
Every effective local-access level is unchanged by exact child-tag removal;
therefore exposed Read/Write contributor support cannot change. -/
theorem levels (tree : BorrowTree) (location : LocationTree) (tags : ProtectedTags)
    (child : UniIndex) (childNode : TreeNode)
    (formed : GeneralBorrowStructuralHistoryState.GraphState tree)
    (present : tree.nodeAt child = some childNode) (held : tags.contains childNode.tag = true)
    (old : DuplicatePrefixBorrowAuthorization.Normal tree location tags child)
    (index : UniIndex) (node : TreeNode) (found : tree.nodeAt index = some node) :
    ((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess
      ((tags.remove childNode.tag).contains node.tag) =
    ((location.perms.get index).getD node.defaultLocationState).permission.strongestAllowedLocalAccess
      (tags.contains node.tag) := by
  by_cases same : index = child
  · subst index
    have equal := Option.some.inj (found.symm.trans present)
    subst node
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
    change _ = ((location.perms.get child).getD childNode.defaultLocationState).permission.strongestAllowedLocalAccess (tags.contains childNode.tag)
    rw [held]
    exact child_level tree location tags child childNode present held old
  · have different : node.tag ≠ childNode.tag := by
      intro sameTag
      have first := formed.allocator.nodeTags index node found
      have second := formed.allocator.nodeTags child childNode present
      rw [sameTag,second] at first
      exact same (Option.some.inj first.symm)
    rw [contains_other tags childNode.tag node.tag different]
end DuplicatePrefix.GeneralBorrowParentRestoreSupport
