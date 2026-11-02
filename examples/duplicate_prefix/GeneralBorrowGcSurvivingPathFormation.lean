import duplicate_prefix.GeneralBorrowGcSurvivingPathPlan
import duplicate_prefix.GeneralBorrowGcDfsForestFormation
import duplicate_prefix.GeneralBorrowGcStarComplete

namespace DuplicatePrefix.GeneralBorrowGcSurvivingPathFormation
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
open DuplicatePrefix.GeneralBorrowGcDfsStage DuplicatePrefix.GeneralBorrowGcStrictChildren
open DuplicatePrefix.GeneralBorrowGcDfsPending DuplicatePrefix.GeneralBorrowGcDfsIncoming
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Exact surviving ancestor membership through the REAL full component walk.
The original reciprocal Forest forms the actual traversal metadata/schedule;
no successful step, Plan or final ancestor relation is supplied. -/
theorem children (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (closed : GeneralBorrowGraph.ChildNodes tree)
    (root : UniIndex) (node : TreeNode) (present : tree.nodes.get root = some node) (live : Array BorTag) :
    ∃ after,source_gc_children tree root live = ⟨after,.ok ()⟩ ∧
      GeneralBorrowGcSurvivingPaths.Valid tree.nodes after.nodes := by
  obtain ⟨final,count,plan,budget⟩ := GeneralBorrowGcDfsFormation.plan tree location protections forest closed root node present
  let metadata := GeneralBorrowGcDfsReadyFormation.metadata tree location protections forest closed
  have backlinks := GeneralBorrowGcDfsBacklinks.of_forest tree location protections forest depth
  have ranked : Ranked (fun index => forest.rank index.toNat) tree := by
    intro index current lookup child member
    obtain ⟨childNode,childPresent,childEdge⟩ := metadata.children index current lookup child member
    exact (GeneralBorrowGcDfsParentPaths.original_edge tree location protections forest child childNode childPresent index childEdge).2
  have stage : Stage tree [] tree := ⟨by intro index outside;rfl,by intro index member;simp at member⟩
  obtain ⟨after,actual,_,_,_,_,_,_,paths⟩ := GeneralBorrowGcSurvivingPathPlan.execute
    (fun index => forest.rank index.toNat) tree tree root live metadata backlinks plan tree 0 stage ranked
    (GeneralBorrowGcDfsPending.initial tree) (GeneralBorrowGcDfsReciprocalStage.initial tree)
    (GeneralBorrowGcDfsIncoming.initial tree) (GeneralBorrowGcSurvivingPaths.initial tree.nodes depth) (by simpa using budget)
  refine ⟨after,?_,paths⟩
  rw [GeneralBorrowGcWalker.children_equation,actual]

/-- FULL production GC over a single listed root preserves ancestry iff at
EVERY surviving source/query. Trim/merge change no node map. This is structural
preservation, not a caller-assumed post-GC relation. -/
theorem single (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection tree location protections).topology)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (closed : GeneralBorrowGraph.ChildNodes tree)
    (root : UniIndex) (node : TreeNode) (present : tree.nodes.get root = some node) (roots : tree.roots = #[root]) (live : Array BorTag) :
    GeneralBorrowGcSurvivingPaths.Valid tree.nodes (tree.removeUnreachableTags live).tree.nodes := by
  obtain ⟨after,actual,paths⟩ := children tree location protections forest depth closed root node present live
  have success : (source_gc_children tree root live).outcome = .ok () := by rw [actual]
  have frame := GeneralBorrowGcStarComplete.nodes tree root live roots success
  have same : (tree.removeUnreachableTags live).tree.nodes = after.nodes := by simpa only [actual] using frame
  rw [same]
  exact paths

end
end DuplicatePrefix.GeneralBorrowGcSurvivingPathFormation
