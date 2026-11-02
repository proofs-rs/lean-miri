import duplicate_prefix.GeneralBorrowSparseExposedLeafState
import duplicate_prefix.GeneralBorrowPartitionExposeCardinality
import duplicate_prefix.GeneralBorrowGcVacantClean
namespace DuplicatePrefix.GeneralBorrowSparseExposedLeafExpose
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSparseExposedLeafState GeneralRangeMapState GeneralBorrowExposureMapFrame GeneralBorrowExposureRelease
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def Scalars (tree : BorrowTree) (protections : ProtectedTags) (location : LocationTree) : Prop :=
  ∀index node,tree.nodeAt index=some node→GeneralBorrowExposedConditionalWritePermissions.Compatible
    (GeneralBorrowWildcardVirtualLeaf.effective location index node) .LocalAccess (protections.contains node.tag)

theorem marked (tree : BorrowTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index=some node) (location : LocationTree) (raw : Scalars tree protections location) :
    Scalars {tree with nodes:=GeneralBorrowExposureMarkGraph.marked tree.nodes index node} protections location := by
  intro query value found
  by_cases same : query=index
  · subst query
    change (tree.nodes.insert index {node with isExposed:=true}).get index=some value at found
    rw [GeneralBorrowFreshLocation.get_same] at found
    cases found
    exact raw index node present
  · change (tree.nodes.insert index {node with isExposed:=true}).get query=some value at found
    rw [GeneralBorrowFreshLocation.get_other _ index query _ same] at found
    exact raw query value found

/-- Actual exposure closes effective mutable scalar data on arbitrary mixed
partitions, including lazy defaults. The real cache update is performed; no
post-exposure cache/profile or operation-success hypothesis is required. -/
theorem expose (tree : BorrowTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index=some node) (tagged : tree.indexOfTag node.tag=some index)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes)
    (raw : Every (fun location=>Raw tree location protections) tree.locations) :
    (tree.exposeTag protections node.tag).outcome=.ok () ∧
    Every (fun location=>Raw (tree.exposeTag protections node.tag).tree location protections) (tree.exposeTag protections node.tag).tree.locations := by
  cases flag : node.isExposed with
  | true => rw [GeneralBorrowRootExposureFrame.already tree node.tag index node tagged present flag protections];exact ⟨rfl,raw⟩
  | false =>
    have coherent : GeneralBorrowPartitionExposeCardinality.Coherent tree protections:=fun position valid=>(raw position valid).1
    have actual:=GeneralBorrowPartitionExposeCardinality.unexposed tree protections index node present tagged depth flag coherent
    let markTree:={tree with nodes:=GeneralBorrowExposureMarkGraph.marked tree.nodes index node}
    let update:=GeneralBorrowPartitionExposeCardinality.callback tree protections index node
    have source : tree.exposeTag protections node.tag=source_location_update markTree update := by
      unfold BorrowTree.exposeTag
      simp only [tagged,present,flag,Bool.false_eq_true,↓reduceIte,Id.run,pure]
      rfl
    have markDepth:=GeneralBorrowExposureMarkGraph.depth tree.nodes depth index node present
    have markPresent : markTree.nodeAt index=some {node with isExposed:=true}:=GeneralBorrowFreshLocation.get_same tree.nodes index _
    have scalar:=GeneralBorrowLocationUpdateProperty.every markTree update (Scalars tree protections) (Scalars markTree protections)
      (fun position valid=>(raw position valid).2) (by
        intro location good
        have success:=GeneralBorrowExposure.update_exposure_succeeds location.exposedCache markTree.nodes markDepth index _ markPresent
          .None (GeneralBorrowExposureCardinality.effective location protections index node)
        refine ⟨?_,?_⟩
        · change (location.exposedCache.updateExposure markTree.nodes index .None
            (GeneralBorrowExposureCardinality.effective location protections index node)).outcome.mapError _=.ok ()
          rw [success];rfl
        · exact marked tree protections index node present location good)
    have allScalars : Every (Scalars markTree protections) (tree.exposeTag protections node.tag).tree.locations := by
      rw [source]
      exact scalar.2
    refine ⟨actual.1,?_⟩
    intro position valid
    refine ⟨actual.2.1 position valid,?_⟩
    have next:=allScalars position valid
    intro query value found
    change (tree.exposeTag protections node.tag).tree.nodes.get query=some value at found
    rw [actual.2.2] at found
    exact next query value found

/-- Source exposure retains actual vacancy cleanliness; changing exposure and
cache fields cannot invent a stored permission at a missing physical node. -/
theorem clean (tree : BorrowTree) (protections : ProtectedTags) (index : UniIndex) (node : TreeNode)
    (present : tree.nodeAt index=some node) (tagged : tree.indexOfTag node.tag=some index)
    (depth : GeneralBorrowExposure.ParentDepth tree.nodes) (initial : GeneralBorrowGcVacantClean.VacantClean tree) :
    GeneralBorrowGcVacantClean.VacantClean (tree.exposeTag protections node.tag).tree := by
  cases flag : node.isExposed with
  | true => rw [GeneralBorrowRootExposureFrame.already tree node.tag index node tagged present flag protections];exact initial
  | false =>
    have shape:=(GeneralBorrowRootExposureFrame.expose tree node.tag index node tagged present depth flag protections).2.1
    intro query vacant
    have lookup:=GeneralBorrowFreshMetadata.lookup_shape tree (tree.exposeTag protections node.tag).tree shape query
    rw [vacant,Option.map_none] at lookup
    have oldVacant : tree.nodes.get query=none := by
      cases found : tree.nodes.get query with
      | none=>rfl
      | some old=>simp [found] at lookup
    exact GeneralBorrowFreshFutureClean.shape_preserves tree _ shape query (initial query oldVacant)
end
end DuplicatePrefix.GeneralBorrowSparseExposedLeafExpose
