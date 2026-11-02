import duplicate_prefix.GeneralBorrowSharedRootBankGc
import duplicate_prefix.GeneralBorrowExposedPartitionState
namespace DuplicatePrefix.GeneralBorrowRootExposureGc
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowView DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- Recursive finite-forest resources are independent of flags and caches. -/
def resources (tree next : BorrowTree) (root : UniIndex)
    (s : GeneralBorrowRecursiveSharedResources.Resources tree root) (shape : treeShape next = treeShape tree) :
    GeneralBorrowRecursiveSharedResources.Resources next root := {
  depth := GeneralBorrowFreshMetadata.parent_depth tree next shape s.depth
  children := GeneralBorrowFreshMetadata.child_nodes tree next shape s.children
  covered := GeneralBorrowFreshMetadata.roots_cover tree next shape s.covered
  roots := (GeneralBorrowFreshMetadata.roots tree next shape).trans s.roots
  allocator := {
    pool := GeneralBorrowFreshStagePool.shape_pool tree next shape s.allocator.pool
    accounting := GeneralBorrowFreshStagePool.shape_accounting tree next shape s.allocator.accounting
    unique := by unfold GeneralBorrowGcAllocator.KeyUnique;rw [GeneralBorrowFreshMetadata.mapping tree next shape];exact s.allocator.unique
    nodeTags := GeneralBorrowSharedAllocatorInvariant.shape_tags tree next shape s.allocator.nodeTags }
  clean := GeneralBorrowPartialSharedClean.shaped tree next shape s.clean
  well := (GeneralBorrowFreshGeometry.shape_frame tree next shape s.well).1
  room := by rw [GeneralBorrowFreshMetadata.node_size tree next shape];exact s.room }

/-- The actual original-root exposure completes on every generated bank. -/
theorem expose {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) :
    (s.bank.tree.exposeTag {} rootTag).outcome = .ok () := by
  obtain ⟨node,present,tagged⟩ := s.rootPresent
  have mapped : s.bank.tree.indexOfTag rootTag = some root := by
    have lookup := s.bank.resources.allocator.nodeTags root node present
    change node.tag = rootTag at tagged
    rw [tagged] at lookup
    exact lookup
  cases flag : node.isExposed with
  | false => exact (GeneralBorrowRootExposureFrame.expose s.bank.tree rootTag root node mapped present s.bank.resources.depth flag {}).1
  | true => rw [GeneralBorrowRootExposureFrame.already s.bank.tree rootTag root node mapped present flag {}]

/-- Actual exposure of the original root, followed by full GC, internally
constructs all next-call resources. This concrete-root invocation frame makes
no wildcard-cache coherence claim. -/
def collect {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (positive : len ≠ 0)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag)
    (reserve : Fin 5 → BorTag) (reserved : ∀ i, GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping (reserve i))
    (live : Array BorTag) :
    GeneralBorrowGcRootResources.Collected (s.bank.tree.exposeTag {} rootTag).tree root rootTag tag offset len reserve live := by
  let tree := s.bank.tree
  let node := Classical.choose s.rootPresent
  have present := (Classical.choose_spec s.rootPresent).1
  have tagged := (Classical.choose_spec s.rootPresent).2
  have mapped : tree.indexOfTag rootTag = some root := by
    have lookup := s.bank.resources.allocator.nodeTags root node present
    change node.tag = rootTag at tagged
    rw [tagged] at lookup
    exact lookup
  have shaped : treeShape (tree.exposeTag {} rootTag).tree = treeShape tree := by
    cases flag : node.isExposed with
    | false => exact (GeneralBorrowRootExposureFrame.expose tree rootTag root node mapped present s.bank.resources.depth flag {}).2.1
    | true => rw [GeneralBorrowRootExposureFrame.already tree rootTag root node mapped present flag {}]
  let next := (tree.exposeTag {} rootTag).tree
  let nextResources := resources tree next root s.bank.resources shaped
  let data := GeneralBorrowSharedRootBankState.entryData s tag fresh
  have owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} root .Write) offset (offset+len) tree.locations := data.owned
  have afterOwned := GeneralBorrowFreshOwnedOn.shape_preserves tree next shaped {} root .Write offset (offset+len) owned
  have fields := GeneralBorrowFreshMetadata.node_fields tree next shaped root node present
  let afterNode := Classical.choose fields
  have afterFacts := Classical.choose_spec fields
  have afterPresent := afterFacts.1
  have afterTag := afterFacts.2.1
  have afterParent := afterFacts.2.2.1
  let location : LocationTree := ⟨⟨#[]⟩,{}⟩
  have forest := GeneralBorrowFreshDefaultPathData.forest_of_owned tree {} root offset len positive s.bank.resources.well s.bank.bounds owned location {}
  have parent := GeneralBorrowGcRootResources.parentless tree root node location forest present (s.rootPath location)
  have geometry := GeneralBorrowFreshGeometry.shape_frame tree next shaped s.bank.resources.well
  exact GeneralBorrowGcRootResources.collect next root rootTag tag offset len nextResources afterNode afterPresent
    (afterTag.trans tagged) (afterParent.trans parent) positive (by rw [geometry.2];exact s.bank.bounds) afterOwned
    (by rw [GeneralBorrowFreshMetadata.mapping tree next shaped];exact fresh) reserve
    (by intro i;rw [GeneralBorrowFreshMetadata.mapping tree next shaped];exact reserved i) live
end
end DuplicatePrefix.GeneralBorrowRootExposureGc
