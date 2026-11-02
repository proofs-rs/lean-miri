import duplicate_prefix.GeneralBorrowObserverReadRange
import duplicate_prefix.GeneralBorrowFreshRootScopedObserverReadRow
import duplicate_prefix.GeneralBorrowFreshRootScopedReadRange
import duplicate_prefix.GeneralBorrowReadReleaseCore
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedObserverReadRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowFreshReleaseLoop
open DuplicatePrefix.GeneralBorrowFreshActiveWithin
open GeneralBorrowObserverReadRow (virtual)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

def Row (tree : BorrowTree) (global : GlobalState) (allocation : AllocId)
    (anchor selected : UniIndex) (maximum : BorTag) (childTag temporaryTag : BorTag) (observer : UniIndex)
    (location : LocationTree) : Prop :=
  GeneralBorrowFreshRootScopedReadRange.Row tree global.protectedTags anchor selected maximum location ∧
  GeneralBorrowObserverReadRange.Observer tree (virtual global allocation childTag temporaryTag) observer location

private theorem location (tree : BorrowTree) (global : GlobalState)
    (beforeRuntime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (anchor selected : UniIndex) (anchorNode : TreeNode) (present : tree.nodeAt anchor = some anchorNode)
    (allocation : AllocId) (temporary observer : UniIndex) (temporaryNode observerNode : TreeNode)
    (childEdge : anchorNode.parent = some temporary)
    (temporaryPresent : tree.nodeAt temporary = some temporaryNode) (temporaryEdge : temporaryNode.parent = some observer)
    (observerPresent : tree.nodeAt observer = some observerNode)
    (childHidden : anchorNode.isExposed = false) (temporaryHidden : temporaryNode.isExposed = false)
    (observerPath : ((source_normal_projection tree default
      (virtual global allocation anchorNode.tag temporaryNode.tag)).topology.ancestorPath observer.toNat).getLast? = some selected.toNat)
    (maximum : BorTag) (current : LocationTree)
    (row : Row tree global allocation anchor selected maximum anchorNode.tag temporaryNode.tag observer current)
    (distinct : tree.roots.toList.Nodup)
    (runtime : GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree global.protectedTags current)
    (short : tree.nodes.size < 65536) (mode : ChildrenVisitMode) (range : ByteRange) :
    let accessed := source_tree_access_at tree current (some anchor) .Read global.protectedTags mode range
    source_access_status accessed = none ∧
    Row tree global allocation anchor selected maximum anchorNode.tag temporaryNode.tag observer (source_access_location accessed) ∧
    GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree global.protectedTags (source_access_location accessed) ∧
    GeneralBorrowSnapshotWildcardRangeBoth.VacantFrame tree current (source_access_location accessed) := by
  obtain ⟨⟨currentRow⟩,⟨currentObserver⟩⟩ := row
  obtain ⟨complete,coherent,profile,possible,afterRow,afterObserver⟩ :=
    GeneralBorrowFreshRootScopedObserverReadRow.access_two_parents tree current global beforeRuntime anchor selected anchorNode present
      allocation temporary observer temporaryNode observerNode childEdge temporaryPresent temporaryEdge observerPresent
      childHidden temporaryHidden currentObserver observerPath maximum currentRow distinct
      runtime.coherent runtime.profile runtime.possible short mode range
  refine ⟨complete,⟨afterRow,afterObserver⟩,⟨coherent,profile,possible⟩,?_⟩
  intro query missing
  rw [profile.vacant query missing,runtime.profile.vacant query missing]

/-- Actual Read-helper release scan retains the original mutable observer
under virtual removal of the helper and shared temporary tags. Every active
callback is derived from current Read-only rows and activity confinement. -/
theorem release (tree : BorrowTree) (global : GlobalState)
    (beforeRuntime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (tag : BorTag) (anchor selected : UniIndex)
    (maximum : BorTag) (lower upper : UInt64) (positive : lower.toNat < upper.toNat)
    (anchorNode : TreeNode) (anchorPresent : tree.nodeAt anchor = some anchorNode) (notExposed : anchorNode.isExposed = false)
    (allocation : AllocId) (temporary observer : UniIndex) (temporaryNode observerNode : TreeNode)
    (childEdge : anchorNode.parent = some temporary)
    (temporaryPresent : tree.nodeAt temporary = some temporaryNode) (temporaryEdge : temporaryNode.parent = some observer)
    (observerPresent : tree.nodeAt observer = some observerNode) (temporaryHidden : temporaryNode.isExposed = false)
    (observerPath : ((source_normal_projection tree default
      (virtual global allocation anchorNode.tag temporaryNode.tag)).topology.ancestorPath observer.toNat).getLast? = some selected.toNat)
    (distinct : tree.roots.toList.Nodup)
    (short : tree.nodes.size < 65536)
    (tagPresent : tree.indexOfTag tag = some anchor)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree anchor .Read lower upper)
    (well : tree.locations.WellFormed)
    (runtime : Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime tree global.protectedTags) tree.locations)
    (owned : OwnedOn (Row tree global allocation anchor selected maximum anchorNode.tag temporaryNode.tag observer) lower upper tree.locations) :
    let result := tree.releaseProtector tag global.protectedTags
    result.status = .Released ∧ result.tree = {tree with locations := result.tree.locations} ∧
      OwnedOn (Row result.tree global allocation anchor selected maximum anchorNode.tag temporaryNode.tag observer) lower upper result.tree.locations ∧
      Every (GeneralBorrowSnapshotWildcardRangeBoth.Runtime result.tree global.protectedTags) result.tree.locations ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin result.tree anchor .Write lower upper ∧
      result.tree.locations.WellFormed ∧ result.tree.locations.size = tree.locations.size := by
  apply GeneralBorrowReadReleaseCore.release tree global.protectedTags tag anchor lower upper positive anchorNode anchorPresent notExposed tagPresent
    (fun current => Row current global allocation anchor selected maximum anchorNode.tag temporaryNode.tag observer)
  · intro map location good
    exact ⟨GeneralBorrowFreshRootScopedReadRange.row_locations tree map location global.protectedTags anchor selected maximum good.1,
      GeneralBorrowObserverReadRange.observer_locations tree map location
        (virtual global allocation anchorNode.tag temporaryNode.tag) observer good.2⟩
  · intro current good currentRuntime range
    obtain ⟨done,rows,afterRuntime,_⟩ := location tree global beforeRuntime anchor selected anchorNode anchorPresent allocation temporary observer temporaryNode observerNode
      childEdge temporaryPresent temporaryEdge observerPresent notExposed temporaryHidden observerPath maximum current good distinct currentRuntime short .SkipChildrenOfAccessed range
    exact ⟨done,rows,afterRuntime⟩
  · exact active
  · exact well
  · exact runtime
  · exact owned
end DuplicatePrefix.GeneralBorrowFreshRootScopedObserverReadRelease
