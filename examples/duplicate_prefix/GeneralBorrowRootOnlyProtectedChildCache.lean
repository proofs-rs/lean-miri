import duplicate_prefix.GeneralBorrowLocalUniqueFrame
import duplicate_prefix.GeneralBorrowRootOnlyStageFrames
import duplicate_prefix.GeneralBorrowDefaultChildState
namespace DuplicatePrefix.GeneralBorrowRootOnlyProtectedChildCache
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowStorage
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 300000

/-- A selected child's real visitor classifies its original root as local. -/
theorem schedule_local (tree : BorrowTree) (location : LocationTree) (root child : UniIndex)
    (rootNode childNode : TreeNode) (rootPresent : tree.nodeAt root = some rootNode) (parentless : rootNode.parent = none)
    (childPresent : tree.nodeAt child = some childNode) (parent : childNode.parent = some root)
    (kind : AccessKind) (mode : ChildrenVisitMode) (protections : ProtectedTags)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) child.toNat kind) :
    ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse child.toNat mode
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2,
      event.node = root.toNat → event.relatedness = .LocalAccess := by
  have paths := GeneralBorrowRootChildWriteOwnership.paths tree location root child rootNode childNode rootPresent parentless childPresent parent
  have inside : root.toNat ∈ (source_normal_projection tree location protections).topology.ancestorPath child.toNat := by
    have childPath : (source_normal_projection tree location protections).topology.ancestorPath child.toNat = [child.toNat,root.toNat] := paths.2
    rw [childPath];simp
  intro event member equal
  have relation := (GeneralBorrowTraversal.traversal_data (source_normal_projection tree location protections).topology forest
    child.toNat owned.anchorValid mode (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2 event member
  simpa only [equal,ite_eq_left inside] using relation.2

/-- Actual child Write leaves root Unique storage and the exact cache intact:
the child is unexposed and the only exposed visitor is a Unique local ancestor. -/
theorem normal (tree : BorrowTree) (location : LocationTree) (root child : UniIndex)
    (rootNode childNode : TreeNode) (rootPresent : tree.nodeAt root = some rootNode) (parentless : rootNode.parent = none)
    (childPresent : tree.nodeAt child = some childNode) (parent : childNode.parent = some root)
    (kind : AccessKind) (mode : ChildrenVisitMode) (protections : ProtectedTags) (only : RootOnly tree root)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology)
    (owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) child.toNat kind)
    (stored : StoredUnique location root) :
    StoredUnique (tree.performNormalAccessAt location child kind protections mode).location root ∧
    (tree.performNormalAccessAt location child kind protections mode).location.exposedCache = location.exposedCache := by
  have localRoot := schedule_local tree location root child rootNode childNode rootPresent parentless childPresent parent kind mode protections forest owned
  refine ⟨GeneralBorrowLocalUniqueFrame.normal_unique tree location protections kind child root rootNode mode rootPresent stored localRoot,?_⟩
  apply GeneralBorrowRootOnlyNormalCache.root_local tree location root child kind protections mode only
    (GeneralBorrowRootOnlyRangeCache.effective tree location root stored)
  have completed := GeneralBorrowTraversal.normal_access _ forest child.toNat kind mode owned
  have visited := GeneralBorrowStorage.events_visited
    ((source_normal_projection tree location protections).topology.traverse child.toNat mode (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2
    ((source_normal_projection tree location protections).topology.traverse child.toNat mode (sourceNormalSkipped (source_normal_projection tree location protections) kind)).1
    kind (source_normal_projection tree location protections) completed
  intro event member equal
  apply localRoot event _ equal
  change ((source_normal_projection tree location protections).performAccess child.toNat kind mode).visited = _ at visited
  rw [←visited]
  exact member

/-- Lift the exact root cache/Unique ancestor frame through the real child-tag
ranged operation and physical partition preparation. -/
theorem ranged (tree : BorrowTree) (root child : UniIndex) (bytes : UInt64) (s : State tree root bytes)
    (childNode : TreeNode) (childPresent : tree.nodeAt child = some childNode) (parent : childNode.parent = some root)
    (tag : BorTag) (tagged : tree.indexOfTag tag = some child) (offset len : UInt64)
    (bounds : offset.toNat+len.toNat ≤ bytes.toNat) (kind : AccessKind) (protections : ProtectedTags)
    (only : RootOnly tree root) (cache : ExposedCache)
    (initial : Every (LocationInvariant cache root) tree.locations)
    (owned : Every (GeneralBorrowRange.LocationOwned tree protections child kind) tree.locations) :
    let after := (tree.performNormalAccessRange tag (Size.ofBytes offset) (Size.ofBytes len) kind protections .VisitChildrenOfAccessed).tree
    RootOnly after root ∧ Every (LocationInvariant cache root) after.locations ∧
      (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed := by
  dsimp only
  have request : (Size.ofBytes offset).bytes.toNat+(Size.ofBytes len).bytes.toNat ≤ tree.locations.size.bytes.toNat := by rw [s.capacity];exact bounds
  have facts := GeneralBorrowRangeProperty.preserves (LocationInvariant cache root) tree protections tag child root
    (Size.ofBytes offset) (Size.ofBytes len) kind kind .VisitChildrenOfAccessed (fun same => same)
    (by have room := s.room;change tree.nodes.data.size+4 ≤ _ at room;omega)
    (GeneralBorrowStarCertificates.depth tree root s.node s.star)
    (GeneralBorrowStarCertificates.children tree root s.node s.star) childNode childPresent s.roots
    (GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots) tagged s.well owned initial (by
      intro location good here
      obtain ⟨⟨forest⟩,owner⟩ := here
      have result := normal tree location root child s.node childNode s.star.present s.star.parentless childPresent parent
        kind .VisitChildrenOfAccessed protections only forest owner good.1
      exact ⟨result.1,result.2.trans good.2⟩) request
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len)
    kind protections .VisitChildrenOfAccessed
  have nodes : (tree.performNormalAccessRange tag (Size.ofBytes offset) (Size.ofBytes len) kind protections .VisitChildrenOfAccessed).tree.nodes = tree.nodes := by
    simpa only [BorrowTree.performNormalAccessRange] using congrArg BorrowTree.nodes frame
  refine ⟨?_,facts.2.1,?_⟩
  · intro index node present exposed
    rw [nodes] at present
    exact only index node present exposed
  · rw [nodes]

end DuplicatePrefix.GeneralBorrowRootOnlyProtectedChildCache
