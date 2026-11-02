import duplicate_prefix.GeneralBorrowGcDfsForestFormation
import duplicate_prefix.GeneralBorrowGcTreeComplete
import duplicate_prefix.GeneralBorrowGcStarComplete
import duplicate_prefix.GeneralBorrowGcNodeMetadata

namespace DuplicatePrefix.GeneralBorrowGcFullForest
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem graph_frame (before after : BorrowTree) (rank : UniIndex → Nat)
    (nodes : after.nodes = before.nodes) (good : GeneralBorrowGcDfsGraphRestoration.Graph rank before) :
    GeneralBorrowGcDfsGraphRestoration.Graph rank after := by
  constructor
  · intro child node present parent edge
    rw [nodes] at present
    obtain ⟨parentNode,parentPresent,member,strict⟩ := good.parents child node present parent edge
    exact ⟨parentNode,by rw [nodes];exact parentPresent,member,strict⟩
  · intro parent node present child member
    rw [nodes] at present
    obtain ⟨childNode,childPresent,edge⟩ := good.children parent node present child member
    exact ⟨childNode,by rw [nodes];exact childPresent,edge⟩
  · intro parent node present
    rw [nodes] at present
    exact good.distinct parent node present

/-- FULL actual removeUnreachableTags with one listed root completes on arbitrary
branching/depth/partitions and forms the actual final reciprocal Forest and
bounded ParentDepth. All surviving tag/default/exposure metadata is unchanged;
no final graph, operation success or intermediate state is a premise. -/
theorem single (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (closed : GeneralBorrowGraph.ChildNodes tree) (fits : tree.nodes.size ≤ 4294967296)
    (root : UniIndex) (node : TreeNode) (present : tree.nodes.get root = some node)
    (roots : tree.roots = #[root]) (well : tree.locations.WellFormed) (live : Array BorTag) :
    (tree.removeUnreachableTags live).outcome = .ok () ∧
    (tree.removeUnreachableTags live).tree.locations.WellFormed ∧
    (tree.removeUnreachableTags live).tree.locations.size = tree.locations.size ∧
    (tree.removeUnreachableTags live).tree.nodes.size = tree.nodes.size ∧
    Nonempty (GeneralBorrowExposure.ParentDepth (tree.removeUnreachableTags live).tree.nodes) ∧
    (∀ nextLocation nextProtections, Nonempty (Forest (source_normal_projection (tree.removeUnreachableTags live).tree nextLocation nextProtections).topology)) ∧
    GeneralBorrowGraph.ChildNodes (tree.removeUnreachableTags live).tree ∧
    GeneralBorrowGcDfsIncoming.Backlinks (tree.removeUnreachableTags live).tree ∧
    GeneralBorrowGcNodeMetadata.Metadata tree (tree.removeUnreachableTags live).tree := by
  obtain ⟨after,actual,graph,_,capacity,_⟩ := GeneralBorrowGcDfsForestFormation.children tree location protections forest depth closed root node present live
  have success : (source_gc_children tree root live).outcome = .ok () := by rw [actual]
  have nodes := GeneralBorrowGcStarComplete.nodes tree root live roots success
  have sameNodes : (tree.removeUnreachableTags live).tree.nodes = after.nodes := by simpa only [actual] using nodes
  have finalGraph := graph_frame after (tree.removeUnreachableTags live).tree _ sameNodes graph
  have finalCapacity : (tree.removeUnreachableTags live).tree.nodes.size = tree.nodes.size := by rw [sameNodes,capacity]
  have finalFits : (tree.removeUnreachableTags live).tree.nodes.size ≤ 4294967296 := by rw [finalCapacity];exact fits
  have completed := GeneralBorrowGcTreeComplete.complete tree location protections forest closed root node live present roots well
  refine ⟨completed.1,completed.2.1,completed.2.2,finalCapacity,
    ⟨GeneralBorrowGcDfsGraphRestoration.depth _ _ finalGraph⟩,?_,?_,?_,GeneralBorrowGcNodeMetadata.collect tree live⟩
  · intro nextLocation nextProtections
    exact ⟨GeneralBorrowGcDfsProjectedForest.of_graph _ _ finalGraph finalFits nextLocation nextProtections⟩
  · intro parent value found child member
    obtain ⟨childNode,childPresent,_⟩ := finalGraph.children parent value found child member
    exact ⟨childNode,childPresent⟩
  · intro child value found parent edge
    obtain ⟨parentNode,parentPresent,member,_⟩ := finalGraph.parents child value found parent edge
    exact ⟨parentNode,parentPresent,member⟩

end DuplicatePrefix.GeneralBorrowGcFullForest
