import duplicate_prefix.GeneralBorrowWildcardRootRowPositive
import duplicate_prefix.GeneralBorrowFreshReuseNode
import duplicate_prefix.GeneralBorrowFreshWriteRestore
namespace DuplicatePrefix.S02WildcardSameDestinationRootTopology
open Miri Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralBorrowPresence GeneralBorrowTopology GeneralBorrowNodeUpdate GeneralBorrowFreshNode
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] UniValMap.insert
/-- A vacant slot and a fresh isolated root project to the same node data. -/
theorem nodes (tree : BorrowTree) (index : UniIndex) (node : TreeNode)
    (vacant : tree.nodes.get index = none) (parentless : node.parent = none) (leaf : node.children = #[])
    (slot : index.toNat = tree.nodes.data.size ∨ index.toNat < tree.nodes.data.size)
    (location : LocationTree) (protections : ProtectedTags) :
    let before := (source_normal_projection tree location protections).topology
    let after := (source_normal_projection {tree with nodes := tree.nodes.insert index node} location protections).topology
    after.nodes = before.nodes ∨ after.nodes = before.nodes.push ⟨none,[]⟩ := by
  rcases slot with atEnd | bounded
  · right
    unfold_general_projection
    unfold_general_topology
    simp only [insert_append tree.nodes index node atEnd,Array.map_push,parentless,leaf,Option.map_some,Option.map_none,Array.toList_empty,List.map_nil]
  · left
    have oldSlot : tree.nodes.data[index.toNat]'bounded = none := by
      simpa only [UniValMap.get,Array.getElem?_eq_getElem bounded] using vacant
    unfold_general_projection
    unfold_general_topology
    rw [GeneralBorrowFreshReuseNode.insert_bounded tree.nodes index node bounded,Array.map_set]
    apply Array.ext
    · simp
    · intro position oldValid newValid
      by_cases equal : position = index.toNat
      · subst position
        simp only [Array.getElem_set_self,Array.getElem_map,parentless,leaf,Option.map_some,Array.toList_empty,List.map_nil,oldSlot,Option.map_none,Option.getD_none]
      · simp only [Array.getElem_set,Array.getElem_map,equal,Ne.symm equal,↓reduceIte]

theorem data (before after : TraversalTree)
    (shape : after.nodes = before.nodes ∨ after.nodes = before.nodes.push ⟨none,[]⟩) :
    ∀ position,nodeData after position = nodeData before position := by
  intro position
  rcases shape with same | append
  · simp only [nodeData,same]
  · by_cases same : position = before.nodes.size
    · simp [nodeData,append,same]
    · simp [nodeData,append,Array.getElem?_push,same]

private theorem at_fuel (before after : TraversalTree)
    (same : ∀ position,nodeData after position = nodeData before position) (fuel anchor : Nat) :
    sourceAncestorPath after fuel anchor = sourceAncestorPath before fuel anchor := by
  induction fuel generalizing anchor with
  | zero => rfl
  | succ fuel ih =>
    rw [ancestor_succ,ancestor_succ,same]
    cases (nodeData before anchor).parent with
    | none => rfl
    | some parent => exact congrArg (List.cons anchor) (ih parent)

private theorem terminal_step (tree : TraversalTree) (fuel anchor : Nat)
    (terminal : (nodeData tree (sourceAncestorPath tree fuel anchor).getLast!).parent = none) :
    sourceAncestorPath tree (fuel+1) anchor = sourceAncestorPath tree fuel anchor := by
  induction fuel generalizing anchor with
  | zero =>
    have edge : (nodeData tree anchor).parent = none := by simpa [ancestor_zero] using terminal
    rw [ancestor_succ,edge,ancestor_zero]
  | succ fuel ih =>
    rw [ancestor_succ] at terminal
    rw [ancestor_succ,ancestor_succ]
    cases edge : (nodeData tree anchor).parent with
    | none => rfl
    | some parent =>
      simp only [edge] at terminal ⊢
      have last : (anchor :: sourceAncestorPath tree fuel parent).getLast! = (sourceAncestorPath tree fuel parent).getLast! := by
        simp only [List.getLast!_eq_getLast?_getD,List.getLast?_cons_of_ne_nil (GeneralBorrowTerminal.ancestors_nonempty tree fuel parent)]
      rw [last] at terminal
      rw [ih parent terminal]

/-- Production ancestor paths also account for the changed append fuel. -/
theorem path (before after : TraversalTree)
    (shape : after.nodes = before.nodes ∨ after.nodes = before.nodes.push ⟨none,[]⟩)
    (forest : GeneralBorrowForest.Forest before) (anchor : Nat) (valid : anchor < before.nodes.size) :
    after.ancestorPath anchor = before.ancestorPath anchor := by
  have same := data before after shape
  unfold TraversalTree.ancestorPath
  rw [at_fuel before after same]
  rcases shape with equal | append
  · rw [equal]
  · rw [append,Array.size_push]
    exact terminal_step before before.nodes.size anchor (GeneralBorrowTerminal.ancestor_terminal before forest anchor valid)
end DuplicatePrefix.S02WildcardSameDestinationRootTopology
