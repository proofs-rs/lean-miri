import duplicate_prefix.GeneralBorrowExposureEntries
namespace DuplicatePrefix.GeneralBorrowExposureMarkGraph
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposure DuplicatePrefix.GeneralBorrowExposureAncestorFold
open DuplicatePrefix.GeneralBorrowNodeUpdate
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def marked (nodes : UniValMap TreeNode) (index : UniIndex) (node : TreeNode) : UniValMap TreeNode :=
  nodes.insert index {node with isExposed := true}

theorem walk_next (nodes : UniValMap TreeNode) (fuel : Nat) (index : UniIndex) :
    walk nodes (fuel+1) index = index :: match (nodes.get index).bind TreeNode.parent with
      | none => [] | some parent => walk nodes fuel parent := by
  simp only [walk]
  cases found : nodes.get index <;> rfl

theorem walk_congr (before after : UniValMap TreeNode)
    (same : ∀ query,(after.get query).bind TreeNode.parent = (before.get query).bind TreeNode.parent)
    (fuel : Nat) (index : UniIndex) : walk after fuel index = walk before fuel index := by
  induction fuel generalizing index with
  | zero => rfl
  | succ fuel ih =>
    rw [walk_next,walk_next,same]
    cases parent : (before.get index).bind TreeNode.parent with
    | none => rfl
    | some earlier => exact congrArg (List.cons index) (ih earlier)

theorem parent (nodes : UniValMap TreeNode) (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node)
    (query : UniIndex) :
    ((marked nodes index node).get query).bind TreeNode.parent = (nodes.get query).bind TreeNode.parent := by
  by_cases same : query = index
  · subst query
    rw [show (marked nodes index node).get index = some {node with isExposed := true} from GeneralBorrowFreshLocation.get_same nodes index _,present]
    rfl
  · rw [show (marked nodes index node).get query = nodes.get query from GeneralBorrowFreshLocation.get_other nodes index query _ same]

theorem walk_mark (nodes : UniValMap TreeNode) (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node)
    (fuel : Nat) (query : UniIndex) : walk (marked nodes index node) fuel query = walk nodes fuel query :=
  walk_congr nodes _ (parent nodes index node present) fuel query

theorem size (nodes : UniValMap TreeNode) (index : UniIndex) (node : TreeNode) (present : nodes.get index = some node) :
    (marked nodes index node).size = nodes.size := insert_existing_size nodes index node _ present

/-- Marking an actual node exposed preserves ParentDepth, without any allocation
or permission constraints and without weakening the finite parent bound. -/
def depth (nodes : UniValMap TreeNode) (good : ParentDepth nodes) (index : UniIndex) (node : TreeNode)
    (present : nodes.get index = some node) : ParentDepth (marked nodes index node) where
  depth := good.depth
  bounded := by
    intro query value found
    rw [size nodes index node present]
    by_cases same : query = index
    · subst query;exact good.bounded index node present
    · have old : nodes.get query = some value := (GeneralBorrowFreshLocation.get_other nodes index query _ same).symm.trans found
      exact good.bounded query value old
  parent := by
    intro query value found before edge
    have oldParent : (nodes.get query).bind TreeNode.parent = some before := by
      rw [←parent nodes index node present query,found]
      exact edge
    cases old : nodes.get query with
    | none =>
      have impossible : (none : Option UniIndex) = some before := by simpa only [old,Option.bind_none] using oldParent
      cases impossible
    | some oldNode =>
      have original : oldNode.parent = some before := by simpa only [old,Option.bind_some] using oldParent
      obtain ⟨earlier,earlierFound,smaller⟩ := good.parent query oldNode old before original
      by_cases same : before = index
      · subst before
        exact ⟨_,GeneralBorrowFreshLocation.get_same nodes index _,smaller⟩
      · exact ⟨earlier,(GeneralBorrowFreshLocation.get_other nodes index before _ same).trans earlierFound,smaller⟩
end DuplicatePrefix.GeneralBorrowExposureMarkGraph
