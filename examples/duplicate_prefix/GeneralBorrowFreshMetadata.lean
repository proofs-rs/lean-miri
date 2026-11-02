import duplicate_prefix.GeneralBorrowView
import duplicate_prefix.GeneralBorrowGraph

/-! Transfer graph certificates across the permission view preserved by actual
SIFA updates. Node default SIFA and exposure flags may differ. -/
namespace DuplicatePrefix.GeneralBorrowFreshMetadata
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowView GeneralBorrowExposure GeneralBorrowGraph
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

theorem mapping (before after : BorrowTree) (same : treeShape after = treeShape before) :
    after.tagMapping = before.tagMapping := congrArg Prod.fst same

theorem roots (before after : BorrowTree) (same : treeShape after = treeShape before) :
    after.roots = before.roots := congrArg (fun shape => shape.2.2.2) same

theorem node_array (before after : BorrowTree) (same : treeShape after = treeShape before) :
    after.nodes.data.map (Option.map nodeShape) = before.nodes.data.map (Option.map nodeShape) :=
  congrArg (fun shape => shape.2.1) same

theorem node_size (before after : BorrowTree) (same : treeShape after = treeShape before) :
    after.nodes.size = before.nodes.size := by
  have eq := congrArg Array.size (node_array before after same)
  simpa only [Array.size_map,UniValMap.size] using eq

theorem map_lookup (nodes : UniValMap TreeNode) (index : UniIndex) :
    (UniValMap.get ⟨nodes.data.map (Option.map nodeShape)⟩ index) =
      (nodes.get index).map nodeShape := by
  simp only [UniValMap.get,Array.getElem?_map]
  cases nodes.data[index.toNat]? <;> rfl

theorem lookup_shape (before after : BorrowTree) (same : treeShape after = treeShape before)
    (index : UniIndex) : (after.nodes.get index).map nodeShape = (before.nodes.get index).map nodeShape := by
  rw [←map_lookup after.nodes index,←map_lookup before.nodes index]
  exact congrArg (fun values => UniValMap.get ⟨values⟩ index) (node_array before after same)

theorem node_exists (before after : BorrowTree) (same : treeShape after = treeShape before)
    (index : UniIndex) (node : TreeNode) (present : before.nodes.get index = some node) :
    ∃ next, after.nodes.get index = some next ∧ nodeShape next = nodeShape node := by
  have eq := lookup_shape before after same index
  rw [present] at eq
  cases lookup : after.nodes.get index with
  | none => simp [lookup] at eq
  | some next => exact ⟨next,rfl,Option.some.inj (by simpa [lookup] using eq)⟩

theorem node_fields (before after : BorrowTree) (same : treeShape after = treeShape before)
    (index : UniIndex) (node : TreeNode) (present : before.nodes.get index = some node) :
    ∃ next, after.nodes.get index = some next ∧ next.tag = node.tag ∧
      next.parent = node.parent ∧ next.children = node.children ∧
      next.defaultInitialPermission = node.defaultInitialPermission := by
  obtain ⟨next,lookup,shape⟩ := node_exists before after same index node present
  exact ⟨next,lookup,congrArg Prod.fst shape,congrArg (fun value => value.2.1) shape,
    congrArg (fun value => value.2.2.1) shape,congrArg (fun value => value.2.2.2) shape⟩

def parent_depth (before after : BorrowTree) (same : treeShape after = treeShape before)
    (depth : ParentDepth before.nodes) : ParentDepth after.nodes where
  depth := depth.depth
  bounded := by
    intro index node present
    obtain ⟨old,lookup,shape⟩ := node_exists after before same.symm index node present
    rw [node_size before after same]
    exact depth.bounded index old lookup
  parent := by
    intro index node present parent edge
    obtain ⟨old,lookup,shape⟩ := node_exists after before same.symm index node present
    have parents : old.parent = node.parent := congrArg (fun shape => shape.2.1) shape
    obtain ⟨earlier,earlierLookup,smaller⟩ := depth.parent index old lookup parent (parents.trans edge)
    obtain ⟨next,nextLookup,_⟩ := node_exists before after same parent earlier earlierLookup
    exact ⟨next,nextLookup,smaller⟩

theorem parent_depth_rank (before after : BorrowTree) (same : treeShape after = treeShape before)
    (depth : ParentDepth before.nodes) : (parent_depth before after same depth).depth = depth.depth := rfl

theorem child_nodes (before after : BorrowTree) (same : treeShape after = treeShape before)
    (children : ChildNodes before) : ChildNodes after := by
  intro index node present child member
  obtain ⟨old,lookup,shape⟩ := node_exists after before same.symm index node present
  have sameChildren : old.children = node.children := congrArg (fun shape => shape.2.2.1) shape
  obtain ⟨oldChild,childLookup⟩ := children index old lookup child (by simpa [sameChildren] using member)
  obtain ⟨next,nextLookup,_⟩ := node_exists before after same child oldChild childLookup
  exact ⟨next,nextLookup⟩

theorem roots_cover (before after : BorrowTree) (same : treeShape after = treeShape before)
    (covered : RootsCover before) : RootsCover after := by
  intro index node present parentless
  obtain ⟨old,lookup,shape⟩ := node_exists after before same.symm index node present
  have parents : old.parent = node.parent := congrArg (fun shape => shape.2.1) shape
  rw [roots before after same]
  exact covered index old lookup (parents.trans parentless)
end DuplicatePrefix.GeneralBorrowFreshMetadata

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.GeneralBorrowFreshMetadata." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved fresh metadata bridge dependency {dependency}"
