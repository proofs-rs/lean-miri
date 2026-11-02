import duplicate_prefix.GeneralBorrowUniqueRootExposure
namespace DuplicatePrefix.GeneralBorrowExposedLeavesRoot
open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposeRead DuplicatePrefix.GeneralBorrowExposeReadFold
open DuplicatePrefix.GeneralBorrowStarExposureCounts DuplicatePrefix.GeneralBorrowExposureHistoryBounds
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Leaf exposure preserves the root and tag mapping exactly. -/
theorem root_frame (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex) (different : ∀ request ∈ requests, root ≠ request.leaf) :
    (pureRun capacity root requests tree location).1.nodeAt root = tree.nodeAt root ∧
    (pureRun capacity root requests tree location).1.tagMapping = tree.tagMapping := by
  induction requests generalizing tree location with
  | nil => exact ⟨rfl,rfl⟩
  | cons request rest ih =>
    have later := ih (nextTree tree location capacity root request) (nextLocation location root request)
      (fun other member => different other (by simp [member]))
    refine ⟨later.1.trans ?_,later.2⟩
    exact GeneralBorrowFreshLocation.get_other tree.nodes request.leaf root _ (different request (by simp))

/-- Actual leaf exposures followed by exposure of the original Unique root.
All final cache values follow from the earlier source-exact leaf fold. -/
theorem expose_after (requests : List Request) (tree : BorrowTree) (location : LocationTree)
    (capacity : UInt64) (root : UniIndex) (rootNode : TreeNode) (rootTag : BorTag) (protections : ProtectedTags)
    (locations : tree.locations = RangeMapNonempty.homogeneous capacity location)
    (ready : ∀ request ∈ requests, Ready tree location root rootNode request)
    (uniqueLeaves : (requests.map Request.leaf).Nodup) (emptyCache : location.exposedCache = {})
    (tagged : tree.indexOfTag rootTag = some root) (rootPresent : tree.nodeAt root = some rootNode)
    (parentless : rootNode.parent = none) (unexposed : rootNode.isExposed = false)
    (rootUnique : ∃ state,location.perms.get root = some state ∧ state.permission = .Unique)
    (room : requests.length+1 < 65536) :
    (run protections requests tree).outcome = .ok () ∧
    ∃ finalLocation, ((run protections requests tree).tree.exposeTag protections rootTag).outcome = .ok () ∧
      ((run protections requests tree).tree.exposeTag protections rootTag).tree.locations =
        RangeMapNonempty.homogeneous capacity finalLocation ∧
      reads finalLocation.exposedCache root = requests.length+1 ∧ writes finalLocation.exposedCache root = 1 ∧
      (∀ leaf ∈ requests.map Request.leaf, reads finalLocation.exposedCache leaf = 1 ∧ writes finalLocation.exposedCache leaf = 0) := by
  have different := fun request member => (ready request member).different
  have actual := run_eq requests tree location capacity root rootNode protections locations ready uniqueLeaves
  have frame := root_frame requests tree location capacity root different
  have counted := pure_counts requests tree location capacity root [] (by rw [emptyCache];exact empty root)
    different (by simp only [List.length_nil,Nat.zero_add];omega)
  simp only [List.append_nil] at counted
  let after := pureRun capacity root requests tree location
  have rootStored : ∃ state,after.2.perms.get root = some state ∧ state.permission = .Unique := by
    rw [show after.2.perms = location.perms from pure_permissions requests tree location capacity root]
    exact rootUnique
  have rootExposure := GeneralBorrowUniqueRootExposure.expose after.1 rootTag root rootNode after.2 capacity protections
    (by change after.1.tagMapping.get rootTag = some root;rw [frame.2];exact tagged)
    (frame.1.trans rootPresent) parentless unexposed rootStored
    (pure_locations requests tree location capacity root locations)
  have finalCounts := GeneralBorrowUniqueRootExposure.counts after.2.exposedCache root _ counted
    (by simpa only [List.length_reverse,List.length_map] using room)
  rw [actual]
  refine ⟨rfl,{after.2 with exposedCache := GeneralBorrowUniqueRootExposure.bump after.2.exposedCache root},?_,?_,?_,finalCounts.2.1,?_⟩
  · rw [rootExposure]
  · rw [rootExposure]
  · simpa only [List.length_reverse,List.length_map] using finalCounts.1
  · intro leaf member
    have notRoot : leaf ≠ root := by
      intro equal
      obtain ⟨request,present,same⟩ := List.mem_map.mp member
      exact different request present (equal.symm.trans same.symm)
    have counts := finalCounts.2.2 leaf notRoot
    refine ⟨counts.1.trans ?_,counts.2⟩
    rw [List.count_reverse]
    exact uniqueLeaves.count_of_mem member
end DuplicatePrefix.GeneralBorrowExposedLeavesRoot
