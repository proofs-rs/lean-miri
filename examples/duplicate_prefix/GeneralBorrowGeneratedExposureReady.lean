import duplicate_prefix.GeneralBorrowGeneratedUnexposed
namespace DuplicatePrefix.GeneralBorrowGeneratedExposureReady
open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGeneratedStarShape DuplicatePrefix.GeneralBorrowSharedUnexposed
open DuplicatePrefix.GeneralBorrowExposeReadFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Recover actual tag/permission Ready metadata for each present star child. -/
theorem child_ready (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (rootNode : TreeNode)
    (star : Star tree root rootNode) (profile : GeneralBorrowSharedGeneratorProfile.Profile tree location root)
    (tags : GeneralBorrowGcAllocator.NodeTags tree) (unexposed : Unexposed tree)
    (leaf : UniIndex) (member : leaf ∈ rootNode.children.toList) :
    ∃ request : Request, request.leaf = leaf ∧ Ready tree location root rootNode request := by
  obtain ⟨different,node,present⟩ := (star.children leaf).mp member
  refine ⟨⟨node.tag,leaf,node⟩,rfl,?_,present,star.present,Ne.symm different,
    (star.leaves leaf node present different).1,star.parentless,unexposed leaf node present,?_⟩
  · exact tags leaf node present
  · exact ⟨GeneralBorrowFreshAnchor.sharedState,profile.shared leaf node present different,rfl⟩

/-- Requests are derived from actual present children, never supplied by the caller. -/
theorem requests (tree : BorrowTree) (location : LocationTree) (root : UniIndex) (rootNode : TreeNode)
    (star : Star tree root rootNode) (profile : GeneralBorrowSharedGeneratorProfile.Profile tree location root)
    (tags : GeneralBorrowGcAllocator.NodeTags tree) (unexposed : Unexposed tree) :
    ∃ requests : List Request, requests.map Request.leaf = rootNode.children.toList ∧
      ∀ request ∈ requests, Ready tree location root rootNode request := by
  have build : ∀ leaves : List UniIndex, (∀ leaf ∈ leaves, leaf ∈ rootNode.children.toList) →
      ∃ requests : List Request, requests.map Request.leaf = leaves ∧
        ∀ request ∈ requests, Ready tree location root rootNode request := by
    intro leaves
    induction leaves with
    | nil => intro included;exact ⟨[],rfl,by simp⟩
    | cons leaf rest ih =>
      intro included
      obtain ⟨request,same,ready⟩ := child_ready tree location root rootNode star profile tags unexposed leaf (included leaf (by simp))
      obtain ⟨later,leaves,laterReady⟩ := ih (fun other member => included other (by simp [member]))
      refine ⟨request::later,?_,?_⟩
      · simp only [List.map_cons,same,leaves]
      · intro other member
        rcases List.mem_cons.mp member with equal | old
        · subst other;exact ready
        · exact laterReady other old
  exact build rootNode.children.toList (fun _ member => member)
end DuplicatePrefix.GeneralBorrowGeneratedExposureReady
