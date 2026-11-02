import duplicate_prefix.GeneralBorrowGcDfsIncomingPlan
import duplicate_prefix.GeneralBorrowGcDfsBacklinks
import duplicate_prefix.GeneralBorrowGcDfsProjectedForest

namespace DuplicatePrefix.GeneralBorrowGcDfsForestFormation
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowForest
open DuplicatePrefix.GeneralBorrowGcDfsStage DuplicatePrefix.GeneralBorrowGcStrictChildren
open DuplicatePrefix.GeneralBorrowGcDfsPending DuplicatePrefix.GeneralBorrowGcDfsIncoming
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Actual arbitrary-component GC completes and reconstructs FULL reciprocal
source graph data, parent existence and bounded ParentDepth. Node origins are
retained. Initial conditions describe the real original finite graph; no Plan,
operation success, intermediate current state or final Forest is supplied. -/
theorem children (original : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection original location protections).topology)
    (depth : GeneralBorrowExposure.ParentDepth original.nodes)
    (closed : GeneralBorrowGraph.ChildNodes original) (root : UniIndex) (node : TreeNode)
    (present : original.nodes.get root = some node) (live : Array BorTag) :
    ∃ after, source_gc_children original root live = ⟨after,.ok ()⟩ ∧
      GeneralBorrowGcDfsGraphRestoration.Graph (fun index => forest.rank index.toNat) after ∧
      Origins original after ∧ after.nodes.size = original.nodes.size ∧ Nonempty (GeneralBorrowExposure.ParentDepth after.nodes) := by
  obtain ⟨final,count,plan,budget⟩ := GeneralBorrowGcDfsFormation.plan original location protections forest closed root node present
  let metadata := GeneralBorrowGcDfsReadyFormation.metadata original location protections forest closed
  have backlinks := GeneralBorrowGcDfsBacklinks.of_forest original location protections forest depth
  have ranked : Ranked (fun index => forest.rank index.toNat) original := by
    intro index current lookup child member
    obtain ⟨childNode,childPresent,childEdge⟩ := metadata.children index current lookup child member
    exact (GeneralBorrowGcDfsParentPaths.original_edge original location protections forest child childNode childPresent index childEdge).2
  have stage : Stage original [] original := ⟨by intro index outside;rfl,by intro index member;simp at member⟩
  obtain ⟨after,actual,finalStage,finalRank,finalPending,finalRepaired,finalIncoming,capacity⟩ := GeneralBorrowGcDfsIncomingPlan.execute
    (fun index => forest.rank index.toNat) original original root live metadata backlinks plan original 0 stage ranked
    (GeneralBorrowGcDfsPending.initial original) (GeneralBorrowGcDfsReciprocalStage.initial original)
    (GeneralBorrowGcDfsIncoming.initial original) (by simpa using budget)
  have graph := GeneralBorrowGcDfsGraphRestoration.restore (fun index => forest.rank index.toNat) original after final metadata backlinks
    finalStage finalRank finalPending finalRepaired finalIncoming
  refine ⟨after,?_,graph,finalIncoming.origins,capacity,⟨GeneralBorrowGcDfsGraphRestoration.depth _ after graph⟩⟩
  rw [GeneralBorrowGcWalker.children_equation,actual]

/-- Actual arbitrary-branching child GC forms the exact real projected Forest
at EVERY location/protector configuration, not a caller-supplied final graph.
The explicit UInt32 slot bound is preserved by the real source walker. -/
theorem children_forest (original : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (forest : Forest (source_normal_projection original location protections).topology)
    (depth : GeneralBorrowExposure.ParentDepth original.nodes)
    (closed : GeneralBorrowGraph.ChildNodes original) (fits : original.nodes.size ≤ 4294967296)
    (root : UniIndex) (node : TreeNode) (present : original.nodes.get root = some node) (live : Array BorTag) :
    ∃ after, source_gc_children original root live = ⟨after,.ok ()⟩ ∧ after.nodes.size = original.nodes.size ∧
      Nonempty (GeneralBorrowExposure.ParentDepth after.nodes) ∧
      (∀ nextLocation nextProtections, Nonempty (Forest (source_normal_projection after nextLocation nextProtections).topology)) ∧
      GeneralBorrowGraph.ChildNodes after ∧ Backlinks after ∧ Origins original after := by
  obtain ⟨after,actual,graph,origins,capacity,afterDepth⟩ := children original location protections forest depth closed root node present live
  have afterFits : after.nodes.size ≤ 4294967296 := by rw [capacity];exact fits
  refine ⟨after,actual,capacity,afterDepth,?_,?_,?_,origins⟩
  · intro nextLocation nextProtections
    exact ⟨GeneralBorrowGcDfsProjectedForest.of_graph after _ graph afterFits nextLocation nextProtections⟩
  · intro parent value found child member
    obtain ⟨childNode,childPresent,_⟩ := graph.children parent value found child member
    exact ⟨childNode,childPresent⟩
  · intro child value found parent edge
    obtain ⟨parentNode,parentPresent,member,_⟩ := graph.parents child value found parent edge
    exact ⟨parentNode,parentPresent,member⟩

end
end DuplicatePrefix.GeneralBorrowGcDfsForestFormation
