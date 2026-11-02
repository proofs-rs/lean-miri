import duplicate_prefix.GeneralBorrowExposureAncestorFold
namespace DuplicatePrefix.GeneralBorrowExposureAncestorDistinct
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureAncestorFold
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Every walked ancestor is present and has no greater data depth. -/
theorem present_depth (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) (fuel : Nat)
    (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node)
    (query : UniIndex) (member : query ∈ walk nodes fuel index) :
    (∃ value,nodes.get query = some value) ∧ depth.depth query ≤ depth.depth index := by
  induction fuel generalizing index node with
  | zero => cases member
  | succ fuel ih =>
    simp only [walk,present,List.mem_cons] at member
    rcases member with same | tail
    · subst query;exact ⟨⟨node,present⟩,Nat.le_refl _⟩
    · cases parent : node.parent with
      | none => simp only [parent,List.not_mem_nil] at tail
      | some before =>
        obtain ⟨earlier,found,smaller⟩ := depth.parent index node present before parent
        rw [parent] at tail
        have facts := ih before earlier found tail
        exact ⟨facts.1,by have := facts.2;omega⟩

/-- ParentDepth excludes repeated ancestors on every finite source walk. -/
theorem nodup (nodes : UniValMap TreeNode) (depth : ParentDepth nodes) (fuel : Nat)
    (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node) :
    (walk nodes fuel index).Nodup := by
  induction fuel generalizing index node with
  | zero => exact List.nodup_nil
  | succ fuel ih =>
    simp only [walk,present]
    cases parent : node.parent with
    | none => dsimp only;exact by simp
    | some before =>
      dsimp only
      obtain ⟨earlier,found,smaller⟩ := depth.parent index node present before parent
      refine List.nodup_cons.mpr ⟨?_,ih before earlier found⟩
      intro repeated
      have facts := present_depth nodes depth fuel before earlier found index repeated
      have impossible := facts.2
      omega
end DuplicatePrefix.GeneralBorrowExposureAncestorDistinct
