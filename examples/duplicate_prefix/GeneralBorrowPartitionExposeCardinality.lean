import duplicate_prefix.GeneralBorrowLocationUpdateFrame
import duplicate_prefix.GeneralBorrowGenericExposeCardinality
namespace DuplicatePrefix.GeneralBorrowPartitionExposeCardinality
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureCardinality
open DuplicatePrefix.GeneralBorrowExposureMarkGraph DuplicatePrefix.GeneralBorrowExposureMapFrame
open DuplicatePrefix.GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Every actual stored range carries its own exposed descendant-cardinality
invariant, using its effective permissions and the actual protection table. -/
def Coherent (tree : BorrowTree) (protections : ProtectedTags) : Prop :=
  Every (fun location => LocationCoherent tree location protections) tree.locations

def callback (tree : BorrowTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (location : LocationTree) : LocationTree × Except BorrowTree.TreeMutationError Unit :=
  let update := location.exposedCache.updateExposure (marked tree.nodes index node) index .None
    (effective location protections index node)
  ({location with exposedCache := update.cache},update.outcome.mapError BorrowTree.TreeMutationError.ExposedCache)

/-- Actual exposeTag adds a contribution at every supporting ancestor on every
stored range of an arbitrary finite ParentDepth forest. Arbitrary partitioning,
permissions and protections are retained; no target-success or cache-output
premise is supplied. -/
theorem unexposed (tree : BorrowTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) (tagged : tree.indexOfTag node.tag = some index)
    (depth : ParentDepth tree.nodes) (unexposed : node.isExposed = false) (initial : Coherent tree protections) :
    (tree.exposeTag protections node.tag).outcome = .ok () ∧
      Coherent (tree.exposeTag protections node.tag).tree protections ∧
      (tree.exposeTag protections node.tag).tree.nodes = marked tree.nodes index node := by
  let markTree := {tree with nodes := marked tree.nodes index node}
  let update := callback tree protections index node
  have markedDepth := GeneralBorrowExposureMarkGraph.depth tree.nodes depth index node present
  have markedPresent : (marked tree.nodes index node).get index = some {node with isExposed := true} := GeneralBorrowFreshLocation.get_same tree.nodes index _
  have each : ∀ location,LocationCoherent tree location protections →
      (update location).2 = .ok () ∧ LocationCoherent markTree (update location).1 protections := by
    intro location coherent
    have success := update_exposure_succeeds location.exposedCache _ markedDepth index _ markedPresent .None
      (effective location protections index node)
    refine ⟨?_,?_⟩
    · change (location.exposedCache.updateExposure (marked tree.nodes index node) index .None
        (effective location protections index node)).outcome.mapError _ = .ok ()
      rw [success];rfl
    · exact GeneralBorrowExposureMarkCardinality.preserves location.exposedCache tree.nodes depth
        (effective location protections) (GeneralBorrowExposureMarkCardinality.effective_stable location protections)
        coherent index node present unexposed
  have all := GeneralBorrowLocationUpdateProperty.every markTree update
    (fun location => LocationCoherent tree location protections)
    (fun location => LocationCoherent markTree location protections) initial each
  have nodes := GeneralBorrowLocationUpdateFrame.nodes markTree update
  have actual : tree.exposeTag protections node.tag = source_location_update markTree update := by
    unfold BorrowTree.exposeTag
    simp only [tagged,present,unexposed,Bool.false_eq_true,↓reduceIte,Id.run,pure]
    rfl
  rw [actual]
  refine ⟨all.1,?_,nodes⟩
  intro position valid
  have locationGood := all.2 position valid
  change GeneralBorrowExposureCardinality.Coherent _ (source_location_update markTree update).tree.nodes _
  rw [nodes]
  exact locationGood

/-- Re-exposure is the real early return; exposure of any valid present tag
preserves the per-range cardinality invariant for arbitrary existing flags. -/
theorem expose (tree : BorrowTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index = some node) (tagged : tree.indexOfTag node.tag = some index)
    (depth : ParentDepth tree.nodes) (initial : Coherent tree protections) :
    (tree.exposeTag protections node.tag).outcome = .ok () ∧ Coherent (tree.exposeTag protections node.tag).tree protections := by
  cases flag : node.isExposed with
  | false =>
    have facts := unexposed tree protections index node present tagged depth flag initial
    exact ⟨facts.1,facts.2.1⟩
  | true =>
    have actual := GeneralBorrowRootExposureFrame.already tree node.tag index node tagged present flag protections
    rw [actual]
    exact ⟨rfl,initial⟩
end DuplicatePrefix.GeneralBorrowPartitionExposeCardinality
