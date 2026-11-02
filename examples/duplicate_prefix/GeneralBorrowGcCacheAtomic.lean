import duplicate_prefix.GeneralBorrowGcCacheContractionCoherent
import duplicate_prefix.GeneralBorrowGcDfsIncomingCollapse

namespace DuplicatePrefix.GeneralBorrowGcCacheAtomic
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureCardinality
open DuplicatePrefix.GeneralBorrowGcCacheContraction
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] UniValMap.insert

/-- Actual sparse leaf deletion has no surviving incoming edge to rewire. -/
def leaf_contract (nodes : UniValMap TreeNode) (removed : UniIndex) (node : TreeNode)
    (present : nodes.get removed = some node)
    (leaf : ∀ query old,nodes.get query = some old → old.parent ≠ some removed) :
    Contract nodes (nodes.remove removed) removed node := by
  refine ⟨present,GeneralBorrowFreshDeassignment.get_removed nodes removed,?_,?_,?_⟩
  · rw [GeneralBorrowSparseRemoval.remove_size]
    exact Nat.le_refl _
  · intro query old found different
    exact ⟨old,(GeneralBorrowSparseRemoval.remove_get_other nodes removed query different).trans found,
      by rw [ite_eq_right (leaf query old found)]⟩
  · intro query value found
    have different : query ≠ removed := by intro same;subst query;rw [GeneralBorrowFreshDeassignment.get_removed] at found;cases found
    exact ⟨different,value,(GeneralBorrowSparseRemoval.remove_get_other nodes removed query different).symm.trans found⟩

def collapsed (nodes : UniValMap TreeNode) (removed replacement : UniIndex)
    (node replacementNode : TreeNode) : UniValMap TreeNode :=
  (nodes.remove removed).insert replacement {replacementNode with parent := node.parent}

/-- This is the EXACT delete-plus-reparent node map of source unary collapse.
Incoming uniqueness is raw repaired-graph data, not a GC outcome premise. -/
def collapse_contract (nodes : UniValMap TreeNode) (removed replacement : UniIndex)
    (node replacementNode : TreeNode) (present : nodes.get removed = some node)
    (childPresent : nodes.get replacement = some replacementNode) (different : replacement ≠ removed)
    (childEdge : replacementNode.parent = some removed)
    (unique : ∀ query old,nodes.get query = some old → old.parent = some removed → query = replacement) :
    Contract nodes (collapsed nodes removed replacement node replacementNode) removed node := by
  have retained := (GeneralBorrowSparseRemoval.remove_get_other nodes removed replacement different).trans childPresent
  have insertSame := GeneralBorrowNodeUpdate.insert_existing_get_same (nodes.remove removed) replacement replacementNode
    {replacementNode with parent := node.parent} retained
  refine ⟨present,?_,?_,?_,?_⟩
  · unfold collapsed
    rw [GeneralBorrowNodeUpdate.insert_existing_get_other _ replacement removed replacementNode _ retained (Ne.symm different),
      GeneralBorrowFreshDeassignment.get_removed]
  · unfold collapsed
    rw [GeneralBorrowNodeUpdate.insert_existing_size _ replacement replacementNode _ retained,GeneralBorrowSparseRemoval.remove_size]
    exact Nat.le_refl _
  · intro query old found outside
    by_cases same : query = replacement
    · subst query
      have eq := Option.some.inj (childPresent.symm.trans found)
      subst old
      exact ⟨_,insertSame,by simp only [childEdge,ite_true]⟩
    · refine ⟨old,?_,?_⟩
      · unfold collapsed
        rw [GeneralBorrowNodeUpdate.insert_existing_get_other _ replacement query replacementNode _ retained same,
          GeneralBorrowSparseRemoval.remove_get_other nodes removed query outside]
        exact found
      · have notEdge : old.parent ≠ some removed := fun edge => same (unique query old found edge)
        rw [ite_eq_right notEdge]
  · intro query value found
    by_cases same : query = replacement
    · subst query
      exact ⟨different,replacementNode,childPresent⟩
    · unfold collapsed at found
      rw [GeneralBorrowNodeUpdate.insert_existing_get_other _ replacement query replacementNode _ retained same] at found
      have outside : query ≠ removed := by intro eq;subst query;rw [GeneralBorrowFreshDeassignment.get_removed] at found;cases found
      exact ⟨outside,value,(GeneralBorrowSparseRemoval.remove_get_other nodes removed query outside).symm.trans found⟩

def clear (location : LocationTree) (removed : UniIndex) : LocationTree :=
  {location with perms := location.perms.remove removed,exposedCache := location.exposedCache.remove removed}

/-- Exact local cache and permission deletion at a genuinely childless node. -/
theorem leaf_coherent (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : ParentDepth tree.nodes) (removed : UniIndex) (node : TreeNode)
    (present : tree.nodes.get removed = some node) (unexposed : node.isExposed = false)
    (leaf : ∀ query old,tree.nodes.get query = some old → old.parent ≠ some removed)
    (initial : LocationCoherent tree location protections) :
    LocationCoherent {tree with nodes := tree.nodes.remove removed} (clear location removed) protections := by
  apply GeneralBorrowGcCacheContractionCoherent.coherent tree.nodes (tree.nodes.remove removed) removed node
    (leaf_contract tree.nodes removed node present leaf) depth unexposed (effective location protections)
    (effective (clear location removed) protections) ?_ location.exposedCache initial
  intro query old found different
  refine ⟨old,(GeneralBorrowSparseRemoval.remove_get_other tree.nodes removed query different).trans found,rfl,?_⟩
  simp only [effective,clear,GeneralBorrowSparseRemoval.remove_get_other _ removed query different]

/-- Exact local cache deletion and old permission frame across the ATOMIC source
unary collapse. Every other ancestor counter remains correct after reparenting. -/
theorem collapse_coherent (tree : BorrowTree) (location : LocationTree) (protections : ProtectedTags)
    (depth : ParentDepth tree.nodes) (removed replacement : UniIndex) (node replacementNode : TreeNode)
    (present : tree.nodes.get removed = some node) (unexposed : node.isExposed = false)
    (childPresent : tree.nodes.get replacement = some replacementNode) (different : replacement ≠ removed)
    (childEdge : replacementNode.parent = some removed)
    (unique : ∀ query old,tree.nodes.get query = some old → old.parent = some removed → query = replacement)
    (initial : LocationCoherent tree location protections) :
    LocationCoherent {tree with nodes := collapsed tree.nodes removed replacement node replacementNode}
      (clear location removed) protections := by
  apply GeneralBorrowGcCacheContractionCoherent.coherent tree.nodes _ removed node
    (collapse_contract tree.nodes removed replacement node replacementNode present childPresent different childEdge unique)
    depth unexposed (effective location protections) (effective (clear location removed) protections) ?_ location.exposedCache initial
  intro query old found outside
  have retained := (GeneralBorrowSparseRemoval.remove_get_other tree.nodes removed replacement different).trans childPresent
  by_cases same : query = replacement
  · subst query
    have eq := Option.some.inj (childPresent.symm.trans found)
    subst old
    refine ⟨{replacementNode with parent := node.parent},?_,rfl,?_⟩
    · exact GeneralBorrowNodeUpdate.insert_existing_get_same _ replacement replacementNode _ retained
    · simp only [effective,clear,GeneralBorrowSparseRemoval.remove_get_other _ removed replacement different]
      rfl
  · refine ⟨old,?_,rfl,?_⟩
    · unfold collapsed
      rw [GeneralBorrowNodeUpdate.insert_existing_get_other _ replacement query replacementNode _ retained same,
        GeneralBorrowSparseRemoval.remove_get_other tree.nodes removed query outside]
      exact found
    · simp only [effective,clear,GeneralBorrowSparseRemoval.remove_get_other _ removed query outside]

end DuplicatePrefix.GeneralBorrowGcCacheAtomic
