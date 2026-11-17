import duplicate_prefix.GeneralBorrowWildcardSubtreeIterator

namespace DuplicatePrefix.GeneralBorrowForestAccessData
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
open GeneralBorrowWildcardSubtreeRegion
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Shared graph/metadata for a concrete source in the primary component,
followed by arbitrary finite extra roots. No singleton-roots restriction. -/
structure Context (tree : BorrowTree) (anchor primary : UniIndex) (extras : List UniIndex) where
  anchorNode : TreeNode
  primaryNode : TreeNode
  depth : GeneralBorrowExposure.ParentDepth tree.nodes
  children : GeneralBorrowGraph.ChildNodes tree
  anchorPresent : tree.nodeAt anchor = some anchorNode
  primaryPresent : tree.nodes.get primary = some primaryNode
  roots : tree.roots = (primary :: extras).toArray
  different : ∀ root ∈ extras, root ≠ primary
  unexposed : ∀ index node, tree.nodes.get index = some node → node.isExposed = false

/-- Per-location initial permissions/cache/finite-forest data. Event exclusion
is a property of the raw topology's traversal schedule, not an access-success
premise. The region may contain arbitrary child-closed extra subtrees. -/
structure LocationData (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (kind : AccessKind) where
  forest : GeneralBorrowForest.Forest (source_normal_projection tree location protections).topology
  owned : GeneralBorrowAnchor.AnchorOwned (source_normal_projection tree location protections) anchor.toNat kind
  rootPath : ((source_normal_projection tree location protections).topology.ancestorPath anchor.toNat).getLast! = primary.toNat
  region : Region tree location kind protections
  supported : ∀ root ∈ extras, region.support root
  outside : ∀ query, region.support query →
    ∀ event ∈ ((source_normal_projection tree location protections).topology.traverse anchor.toNat .VisitChildrenOfAccessed
      (sourceNormalSkipped (source_normal_projection tree location protections) kind)).2, event.node ≠ query.toNat

/-- The actual per-location source operation completes from the graph and
permission/cache records above. All exposed-node flags are static tree data. -/
theorem local_access (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (anchor primary : UniIndex) (extras : List UniIndex) (kind : AccessKind) (range : ByteRange)
    (context : Context tree anchor primary extras)
    (data : LocationData tree location protections anchor primary extras kind) :
    source_access_status (source_tree_access_at tree location (some anchor) kind protections .VisitChildrenOfAccessed range) = none := by
  obtain ⟨after,actual,status,preserved,cache,frame⟩ := GeneralBorrowWildcardSubtreeIterator.access tree location protections
    anchor primary context.anchorNode context.primaryNode extras kind range data.forest data.owned context.depth context.children
    context.anchorPresent context.primaryPresent context.roots context.different data.rootPath data.region data.supported data.outside
    (fun event member index node conversion present => context.unexposed index node present)
  exact status

end DuplicatePrefix.GeneralBorrowForestAccessData
