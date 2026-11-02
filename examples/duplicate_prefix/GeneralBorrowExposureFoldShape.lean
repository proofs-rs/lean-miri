import duplicate_prefix.GeneralBorrowExposureFoldFlags
namespace DuplicatePrefix.GeneralBorrowExposureFoldShape
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposeRead DuplicatePrefix.GeneralBorrowExposeReadFold
open DuplicatePrefix.GeneralBorrowView DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

theorem next_shape (tree : BorrowTree) (location : LocationTree) (capacity : UInt64) (root : UniIndex)
    (request : Request) (node : TreeNode) (present : tree.nodeAt request.leaf = some node)
    (same : nodeShape node = nodeShape request.node)
    (locations : tree.locations = homogeneous capacity location) :
    treeShape (nextTree tree location capacity root request) = treeShape tree := by
  have nodeArray := GeneralBorrowView.insert_existing_shape nodeShape tree.nodes request.leaf node
    {request.node with isExposed := true} present same.symm
  simp only [treeShape,nextTree,marked,nodeArray,locations,homogeneous,Array.map_singleton,
    nextLocation,locationShape]

/-- The fold preserves the whole permission/topology view, while the separate
flag/count theorems retain metadata deliberately omitted by that view. -/
theorem pure_shape (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex)
    (locations : tree.locations = homogeneous capacity location)
    (known : ∀ request ∈ requests,∃ node,tree.nodeAt request.leaf = some node ∧ nodeShape node = nodeShape request.node) :
    treeShape (pureRun capacity root requests tree location).1 = treeShape tree := by
  induction requests generalizing tree location with
  | nil => rfl
  | cons request rest ih =>
    obtain ⟨node,present,same⟩ := known request (by simp)
    have shape := next_shape tree location capacity root request node present same locations
    have later : ∀ other ∈ rest,∃ node,(nextTree tree location capacity root request).nodeAt other.leaf = some node ∧
        nodeShape node = nodeShape other.node := by
      intro other member
      obtain ⟨old,present,same⟩ := known other (by simp [member])
      obtain ⟨next,found,nextShape⟩ := GeneralBorrowFreshMetadata.node_exists tree
        (nextTree tree location capacity root request) shape other.leaf old present
      exact ⟨next,found,nextShape.trans same⟩
    exact (ih _ _ rfl later).trans shape
end DuplicatePrefix.GeneralBorrowExposureFoldShape
