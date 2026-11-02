import duplicate_prefix.GeneralBorrowGcForestComplete
import duplicate_prefix.GeneralBorrowGcAllocatorFull
import duplicate_prefix.GeneralBorrowSharedAllocatorInvariant
import duplicate_prefix.GeneralBorrowFreshGeometry
import duplicate_prefix.GeneralBorrowFullSharedSeed

namespace DuplicatePrefix.GeneralBorrowStructuralHistoryState
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowView GeneralBorrowForest GeneralBorrowExposure GeneralBorrowGraph
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

set_option autoImplicit false in
/-- Intrinsic reciprocal graph and sparse tag allocator data. Neither borrowing
permission validity nor the success of any operation is a field. -/
structure GraphState (tree : BorrowTree) : Prop where
  forest : ∀ location protections, Nonempty (Forest (source_normal_projection tree location protections).topology)
  depth : Nonempty (ParentDepth tree.nodes)
  children : ChildNodes tree
  covered : RootsCover tree
  rootNodes : ∀ root ∈ tree.roots.toList, ∃ node, tree.nodes.get root=some node ∧ node.parent=none
  allocator : GeneralBorrowGcAllocator.Invariant tree
  fits : tree.nodes.size ≤ 4294967296

set_option autoImplicit false in
/-- Structural state also records the real allocation byte partition. -/
structure State (tree : BorrowTree) : Prop extends GraphState tree where
  well : tree.locations.WellFormed

theorem graph_shape (before after : BorrowTree) (same : treeShape after=treeShape before)
    (initial : GraphState before) : GraphState after := by
  have mapping := GeneralBorrowFreshMetadata.mapping before after same
  have capacity := GeneralBorrowFreshMetadata.node_size before after same
  refine ⟨?_,?_,GeneralBorrowFreshMetadata.child_nodes before after same initial.children,
    GeneralBorrowFreshMetadata.roots_cover before after same initial.covered,?_,?_,by rw[capacity];exact initial.fits⟩
  · intro location protections
    have topology := congrArg Prod.fst (GeneralBorrowFreshOwnership.projection_shape before after location location protections
      (GeneralBorrowFreshMetadata.node_array before after same) rfl)
    change (source_normal_projection after location protections).topology = (source_normal_projection before location protections).topology at topology
    rw [topology]
    exact initial.forest location protections
  · obtain ⟨depth⟩ := initial.depth
    exact ⟨GeneralBorrowFreshMetadata.parent_depth before after same depth⟩
  · intro root member
    rw [GeneralBorrowFreshMetadata.roots before after same] at member
    obtain ⟨old,present,parentless⟩ := initial.rootNodes root member
    obtain ⟨node,found,_,parent,_,_⟩ := GeneralBorrowFreshMetadata.node_fields before after same root old present
    exact ⟨node,found,parent.trans parentless⟩
  · refine ⟨GeneralBorrowFreshStagePool.shape_pool before after same initial.allocator.pool,
      GeneralBorrowFreshStagePool.shape_accounting before after same initial.allocator.accounting,?_,
      GeneralBorrowSharedAllocatorInvariant.shape_tags before after same initial.allocator.nodeTags⟩
    rw [mapping]
    exact initial.allocator.unique

theorem shape (before after : BorrowTree) (same : treeShape after=treeShape before)
    (initial : State before) : State after :=
  ⟨graph_shape before after same initial.toGraphState,(GeneralBorrowFreshGeometry.shape_frame before after same initial.well).1⟩

/-- A location-only operation preserves the complete graph/allocator state on
either operational outcome. This assertion does not certify access success. -/
theorem graph_locations (tree : BorrowTree) (locations : DedupRangeMap LocationTree)
    (initial : GraphState tree) : GraphState {tree with locations:=locations} := by
  refine ⟨?_,initial.depth,initial.children,initial.covered,initial.rootNodes,?_,initial.fits⟩
  · intro location protections
    exact initial.forest location protections
  · exact GeneralBorrowGcAllocatorFull.locations_preserves tree locations initial.allocator

/-- Full actual collection derives its successful outcome AND reconstructs the
same intrinsic State at arbitrary reciprocal branching, roots and live tags. -/
theorem gc (tree : BorrowTree) (initial : State tree) (live : Array BorTag) :
    (tree.removeUnreachableTags live).outcome=.ok () ∧ State (tree.removeUnreachableTags live).tree ∧
    (tree.removeUnreachableTags live).tree.locations.size=tree.locations.size := by
  let location : LocationTree := ⟨{},{}⟩
  obtain ⟨forest⟩ := initial.forest location {}
  obtain ⟨depth⟩ := initial.depth
  obtain ⟨completed,well,bytes,capacity,nextDepth,nextForest,nextChildren,_,_,roots⟩ :=
    GeneralBorrowGcForestComplete.complete tree location {} forest depth initial.children initial.fits initial.rootNodes initial.well live
  have rootsEq := (GeneralBorrowGcResourceFrame.preserves (n:=0) (fun step => Fin.elim0 step) tree live
    (by intro step;exact Fin.elim0 step)).roots
  refine ⟨completed,⟨⟨nextForest,nextDepth,nextChildren,GeneralBorrowGcNodeMetadata.roots_cover tree live initial.covered,?_,
    GeneralBorrowGcAllocatorFull.preserves tree live initial.allocator,by rw[capacity];exact initial.fits⟩,well⟩,bytes⟩
  intro root member
  rw [rootsEq] at member
  exact roots root member
end DuplicatePrefix.GeneralBorrowStructuralHistoryState
