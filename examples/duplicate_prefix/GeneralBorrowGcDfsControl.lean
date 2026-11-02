import duplicate_prefix.GeneralBorrowGcDfsChildStage

namespace DuplicatePrefix.GeneralBorrowGcDfsControl
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Exact contextual descent, retaining arbitrary suspended ancestor cursors.
The source counter bound is explicit here and will follow from the finite
original-forest postorder schedule in the whole-walk theorem. -/
theorem descend (seed tree : BorrowTree) (root index : UniIndex) (node : TreeNode)
    (live : Array BorTag) (stack : Array (UniIndex × Nat)) (cursor steps : Nat)
    (present : tree.nodes.get index = some node) (inside : cursor < node.children.size)
    (budget : steps+1 ≤ tree.nodes.size*2+1) :
    outerScan seed root live () (none,tree,stack.push (index,cursor),steps) =
      .yield (none,tree,(stack.push (index,cursor+1)).push (node.children[cursor],0),steps+1) := by
  have counter : ¬ (steps+1 > tree.nodes.size*2+1) := by omega
  simp [outerScan,counter,present,inside,pure]

/-- Exact contextual postvisit: the actual child callback fold and original
error branches remain visible. This is a source equation, not a replacement
with an assumed successful fold. -/
theorem finish_equation (seed tree : BorrowTree) (root index : UniIndex) (node : TreeNode)
    (live : Array BorTag) (stack : Array (UniIndex × Nat)) (cursor steps : Nat)
    (present : tree.nodes.get index = some node) (finished : ¬ cursor < node.children.size)
    (budget : steps+1 ≤ tree.nodes.size*2+1) :
    outerScan seed root live () (none,tree,stack.push (index,cursor),steps) =
      let folded := forIn (m := Id) node.children (none,tree,#[]) (childScan seed root live index)
      match folded.1 with
      | some result => .done (some result,folded.2.1,stack.push (index,cursor),steps+1)
      | none => match folded.2.1.nodes.get index with
        | some currentNode => .yield (none,
            {folded.2.1 with nodes := folded.2.1.nodes.insert index {currentNode with children := folded.2.2}},stack,steps+1)
        | none => .done (some ⟨folded.2.1,.error (.MissingNode index)⟩,folded.2.1,stack.push (index,cursor),steps+1) := by
  have counter : ¬ (steps+1 > tree.nodes.size*2+1) := by omega
  simp [outerScan,counter,present,finished,pure]
  fold_gc_child_callback (seed,root,live,index)
  generalize folded : forIn (m := Id) node.children (none,tree,#[]) (childScan seed root live index) = result
  rcases result with ⟨answer,current,kept⟩
  cases answer with
  | some answer => rfl
  | none => cases found : current.nodes.get index <;> simp only [bind,pure,found]
end DuplicatePrefix.GeneralBorrowGcDfsControl
