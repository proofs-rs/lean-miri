import duplicate_prefix.GeneralBorrowStructuralHistoryGraphFrame
import duplicate_prefix.GeneralBorrowFreshGeometry
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryGraphOperations
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowStructuralHistoryGraphFrame
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- An arbitrary materialization callback, not just one homogeneous permission,
retains structural State and exact allocation capacity on a raw bounded range. -/
theorem modify_range (tree : BorrowTree) (initial : State tree) (offset len : Size)
    (modify : ByteRange → LocationTree → LocationTree)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤tree.locations.size.bytes.toNat) :
    State {tree with locations:=(tree.locations.modifyRange offset len modify).state} ∧
    (tree.locations.modifyRange offset len modify).state.size=tree.locations.size := by
  have geometry := GeneralBorrowFreshRangeFrame.modifyRange_frame tree.locations offset len modify initial.well bounds
  exact ⟨⟨graph_locations tree _ initial.toGraphState,geometry.1⟩,congrArg Size.mk geometry.2⟩

/-- Real ancestor SIFA propagation may change default SIFA and byte-local state;
its structural closure follows from the actual source view theorem. -/
theorem sifa (tree : BorrowTree) (initial : State tree) (parent : UniIndex) (minimum : IdempotentForeignAccess) :
    State (sourceUpdateSifa tree parent minimum).1 ∧
    (sourceUpdateSifa tree parent minimum).1.locations.size=tree.locations.size := by
  have same := GeneralBorrowSifaView.preserves tree parent minimum
  exact ⟨GeneralBorrowStructuralHistoryState.shape tree _ same initial,
    (GeneralBorrowFreshGeometry.shape_frame tree _ same initial.well).2⟩

/-- The stricter permission view implies the minimal graph-only frame, which
can also be established directly for constructors with arbitrary defaults. -/
theorem of_shape (before after : BorrowTree) (same : GeneralBorrowView.treeShape after=GeneralBorrowView.treeShape before) :
    Frame before after := by
  refine ⟨GeneralBorrowFreshMetadata.mapping before after same,?_,GeneralBorrowFreshMetadata.roots before after same⟩
  have shapes := GeneralBorrowFreshMetadata.node_array before after same
  have viewed := congrArg (fun nodes => nodes.map (Option.map (fun value : GeneralBorrowView.NodeShape => (value.1,value.2.1,value.2.2.1)))) shapes
  simp only [Array.map_map,Option.map_map,Function.comp_def,GeneralBorrowView.nodeShape] at viewed
  change after.nodes.data.map (Option.map (fun node=>(node.tag,node.parent,node.children))) = before.nodes.data.map (Option.map (fun node=>(node.tag,node.parent,node.children)))
  exact viewed
end DuplicatePrefix.GeneralBorrowStructuralHistoryGraphOperations
