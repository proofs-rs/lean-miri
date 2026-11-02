import duplicate_prefix.GeneralBorrowGcStarComplete
import duplicate_prefix.GeneralBorrowGcStarWalk
import duplicate_prefix.GeneralBorrowGcLeafShape
import duplicate_prefix.GeneralBorrowGeneratedStarShape

namespace DuplicatePrefix.GeneralBorrowGcStarShape
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
open DuplicatePrefix.GeneralBorrowGeneratedStarShape
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The real postorder walker deletes leaves and rebuilds exactly the surviving
root child list. It retains reciprocal star topology, not just node permissions. -/
theorem children (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (live : Array BorTag)
    (good : Star tree root node) :
    ∃ next, Star (source_gc_children tree root live).tree root next := by
  have leaves : ∀ index ∈ node.children.toList, ∃ child,
      tree.nodes.get index = some child ∧ child.children = #[] := by
    intro index member
    obtain ⟨different,child,present⟩ := (good.children index).mp member
    exact ⟨child,present,(good.leaves index child present different).2⟩
  have notChild : root ∉ node.children.toList := fun member => ((good.children root).mp member).1 rfl
  obtain ⟨after,kept,walked,rootPresent,size,folded⟩ := GeneralBorrowGcStarWalk.complete tree root node live
    good.present good.distinct notChild leaves (children_bound tree root node good)
  obtain ⟨other,result,foldedOther,_,outside,shrinks,distinct,members⟩ :=
    GeneralBorrowGcLeafShape.complete node.children.toList tree tree root root live good.distinct leaves
  have same : (none,after,kept) = (none,other,result) := folded.symm.trans foldedOther
  have trees := congrArg (fun state : ChildState => state.2.1) same
  have lists := congrArg (fun state : ChildState => state.2.2) same
  change after = other at trees
  change kept = result at lists
  subst other
  subst result
  rw [walked]
  refine ⟨{node with children := kept},?_,good.parentless,?_,distinct,?_⟩
  · exact GeneralBorrowNodeUpdate.insert_existing_get_same after.nodes root node _ rootPresent
  · intro query value present different
    change (after.nodes.insert root {node with children := kept}).get query = some value at present
    rw [GeneralBorrowNodeUpdate.insert_existing_get_other after.nodes root query node _ rootPresent different] at present
    exact good.leaves query value (shrinks query value present) different
  · intro query
    rw [members]
    constructor
    · rintro ⟨member,value,present⟩
      have different := ((good.children query).mp member).1
      exact ⟨different,value,(GeneralBorrowNodeUpdate.insert_existing_get_other after.nodes root query node _ rootPresent different).trans present⟩
    · rintro ⟨different,value,present⟩
      change (after.nodes.insert root {node with children := kept}).get query = some value at present
      rw [GeneralBorrowNodeUpdate.insert_existing_get_other after.nodes root query node _ rootPresent different] at present
      exact ⟨(good.children query).mpr ⟨different,value,shrinks query value present⟩,value,present⟩

/-- Full production GC preserves reciprocal star topology after the successful
root walk and its location-only postprocessing. -/
theorem preserves (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (live : Array BorTag)
    (good : Star tree root node) (roots : tree.roots = #[root]) :
    ∃ next, Star (tree.removeUnreachableTags live).tree root next := by
  obtain ⟨next,star⟩ := children tree root node live good
  have leaves : ∀ index ∈ node.children.toList, ∃ child,
      tree.nodes.get index = some child ∧ child.children = #[] := by
    intro index member
    obtain ⟨different,child,present⟩ := (good.children index).mp member
    exact ⟨child,present,(good.leaves index child present different).2⟩
  have notChild : root ∉ node.children.toList := fun member => ((good.children root).mp member).1 rfl
  obtain ⟨_,_,walked,_⟩ := GeneralBorrowGcStarWalk.complete tree root node live good.present good.distinct
    notChild leaves (children_bound tree root node good)
  have success : (source_gc_children tree root live).outcome = .ok () := by rw [walked]
  exact ⟨next,of_nodes _ _ root next (GeneralBorrowGcStarComplete.nodes tree root live roots success) star⟩


end DuplicatePrefix.GeneralBorrowGcStarShape
