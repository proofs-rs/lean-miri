import duplicate_prefix.GeneralBorrowStructuralHistoryState
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryGraphFrame
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState GeneralBorrowExposure GeneralBorrowGraph GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def nodeView (node : TreeNode) := (node.tag,node.parent,node.children)
def nodesView (tree : BorrowTree) := tree.nodes.data.map (Option.map nodeView)

/-- The intrinsic graph view deliberately omits default permissions, SIFA,
exposure and all per-byte state. Those are separate permission-history data. -/
structure Frame (before after : BorrowTree) : Prop where
  mapping : after.tagMapping=before.tagMapping
  nodes : nodesView after=nodesView before
  roots : after.roots=before.roots

private theorem lookup (tree : BorrowTree) (index : UniIndex) :
    (UniValMap.get ⟨nodesView tree⟩ index)=(tree.nodes.get index).map nodeView := by
  simp only [nodesView,UniValMap.get,Array.getElem?_map]
  cases tree.nodes.data[index.toNat]? <;> rfl

theorem capacity (before after : BorrowTree) (same : Frame before after) : after.nodes.size=before.nodes.size := by
  have count := congrArg Array.size same.nodes
  simpa only [nodesView,Array.size_map,UniValMap.size] using count

theorem lookup_view (before after : BorrowTree) (same : Frame before after) (index : UniIndex) :
    (after.nodes.get index).map nodeView=(before.nodes.get index).map nodeView := by
  rw [←lookup after index,←lookup before index,same.nodes]

theorem node_fields (before after : BorrowTree) (same : Frame before after) (index : UniIndex) (node : TreeNode)
    (present : before.nodes.get index=some node) :
    ∃next,after.nodes.get index=some next ∧ next.tag=node.tag ∧ next.parent=node.parent ∧ next.children=node.children := by
  have known := lookup_view before after same index
  rw [present] at known
  cases found : after.nodes.get index with
  | none => simp [found] at known
  | some next =>
    have equal : nodeView next=nodeView node := Option.some.inj (by simpa only [found,Option.map_some] using known)
    exact ⟨next,rfl,congrArg Prod.fst equal,congrArg (fun value=>value.2.1) equal,congrArg (fun value=>value.2.2) equal⟩

theorem reverse (before after : BorrowTree) (same : Frame before after) : Frame after before :=
  ⟨same.mapping.symm,same.nodes.symm,same.roots.symm⟩

private def topology (nodes : Array (Option (BorTag × Option UniIndex × Array UniIndex))) : TraversalTree :=
  ⟨nodes.map fun cell => match cell with
    | none => ⟨none,[]⟩
    | some (_,parent,children) => ⟨parent.map UniIndex.toNat,children.toList.map UniIndex.toNat⟩⟩

private theorem topology_factor (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags) :
    (source_normal_projection tree location protections).topology=topology (nodesView tree) := by
  unfold_general_projection
  unfold_general_topology
  simp only [topology,nodesView,Array.map_map,Function.comp_def]
  congr 2
  funext cell
  cases cell <;> rfl

/-- Sparse graph, root and allocator invariants survive arbitrary permission,
SIFA/exposure and range-state changes that retain only this minimal view. -/
theorem graph (before after : BorrowTree) (same : Frame before after) (initial : GraphState before) : GraphState after := by
  have size := capacity before after same
  have backwards := reverse before after same
  refine ⟨?_,?_,?_,?_,?_,?_,by rw[size];exact initial.fits⟩
  · intro location protections
    rw [topology_factor,same.nodes,←topology_factor before location protections]
    exact initial.forest location protections
  · obtain ⟨depth⟩ := initial.depth
    refine ⟨{depth:=depth.depth,bounded:=?_,parent:=?_}⟩
    · intro index node present
      obtain ⟨old,found,_,_,_⟩ := node_fields after before backwards index node present
      rw [size]
      exact depth.bounded index old found
    · intro index node present parent edge
      obtain ⟨old,found,_,parents,_⟩ := node_fields after before backwards index node present
      obtain ⟨earlier,ancestor,smaller⟩ := depth.parent index old found parent (parents.trans edge)
      obtain ⟨next,nextFound,_,_,_⟩ := node_fields before after same parent earlier ancestor
      exact ⟨next,nextFound,smaller⟩
  · intro index node present child member
    obtain ⟨old,found,_,_,children⟩ := node_fields after before backwards index node present
    obtain ⟨oldChild,childFound⟩ := initial.children index old found child (by rw[children];exact member)
    obtain ⟨next,nextFound,_,_,_⟩ := node_fields before after same child oldChild childFound
    exact ⟨next,nextFound⟩
  · intro index node present parentless
    obtain ⟨old,found,_,parents,_⟩ := node_fields after before backwards index node present
    rw [same.roots]
    exact initial.covered index old found (parents.trans parentless)
  · intro root member
    rw [same.roots] at member
    obtain ⟨old,present,parentless⟩ := initial.rootNodes root member
    obtain ⟨next,found,_,parents,_⟩ := node_fields before after same root old present
    exact ⟨next,found,parents.trans parentless⟩
  · refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
    · intro index member
      change index.toNat < after.nodes.size
      rw [size]
      exact initial.allocator.pool.bounded index (by rw[same.mapping] at member;exact member)
    · intro index member
      have vacant := initial.allocator.pool.vacant index (by rw[same.mapping] at member;exact member)
      have absent := lookup_view before after same index
      rw [vacant] at absent
      cases found : after.nodes.get index with
      | none => rfl
      | some node => simp [found] at absent
    · rw [same.mapping]
      exact initial.allocator.pool.nodup
    · unfold GeneralBorrowFreshStagePool.Accounting
      rw [same.mapping,size]
      exact initial.allocator.accounting
    · rw [same.mapping]
      exact initial.allocator.unique
    · intro index node present
      obtain ⟨old,found,tag,_,_⟩ := node_fields after before backwards index node present
      rw [same.mapping,←tag]
      exact initial.allocator.nodeTags index old found
end DuplicatePrefix.GeneralBorrowStructuralHistoryGraphFrame
