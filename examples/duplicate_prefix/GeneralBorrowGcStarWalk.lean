import duplicate_prefix.GeneralBorrowGcLeafFold
import duplicate_prefix.GeneralBorrowGcWalker
import duplicate_prefix.GeneralBorrowGcChildFold
import duplicate_prefix.GeneralBorrowLoop

namespace DuplicatePrefix.GeneralBorrowGcStarWalk
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcChildFold
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

private theorem insert_same {α : Type} (nodes : UniValMap α) (index : UniIndex) (value : α)
    (present : nodes.get index = some value) : nodes.insert index value = nodes := by
  have valid := GeneralBorrowNodeUpdate.lookup_valid nodes index value present
  have entry : nodes.data[index.toNat] = some value := by
    unfold UniValMap.get at present
    simpa only [Array.getElem?_eq_getElem valid] using present
  have same := GeneralBorrowNodeUpdate.insert_existing nodes index value value present
  rw [←entry,Array.set_getElem_self] at same
  cases nodes with
  | mk original =>
    cases result : (UniValMap.mk original).insert index value with
    | mk changed => exact congrArg UniValMap.mk (by simpa only [result] using same)

/-- Descending from the root to its next leaf consumes one actual source step. -/
theorem descend (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (live : Array BorTag)
    (present : tree.nodes.get root = some node) (i : Nat) (inside : i < node.children.size)
    (bounded : node.children.size ≤ tree.nodes.size) :
    outerScan tree root live () (none,tree,#[(root,i)],2*i) =
      .yield (none,tree,#[(root,i+1),(node.children[i],0)],2*i+1) := by
  have counter : ¬ (2*i+1 > tree.nodes.size*2+1) := by omega
  simp [outerScan,counter,present,inside,pure]

/-- Processing a childless node performs the real empty child fold and an
identity node rewrite, then returns to the root without changing the tree. -/
theorem leaf (tree : BorrowTree) (root child : UniIndex) (node : TreeNode) (live : Array BorTag)
    (present : tree.nodes.get child = some node) (empty : node.children = #[]) (i : Nat)
    (bounded : 2*i+2 ≤ tree.nodes.size*2+1) :
    outerScan tree root live () (none,tree,#[(root,i+1),(child,0)],2*i+1) =
      .yield (none,tree,#[(root,i+1)],2*(i+1)) := by
  have counter : ¬ (2*i+1+1 > tree.nodes.size*2+1) := by omega
  have same : {node with children := #[]} = node := by cases node;simp_all
  have inserted := insert_same tree.nodes child node present
  have arithmetic : 2*i+1+1 = 2*(i+1) := by omega
  have normalized : ¬ tree.nodes.size*2+1 < 2*(i+1) := by omega
  simp [outerScan,normalized,present,empty,same,inserted,arithmetic,pure,bind]

/-- The production traversal visits every leaf of an explicit star before any
root child removal. The symbolic execution is independent of the live-tag set. -/
theorem visit (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (live : Array BorTag)
    (present : tree.nodes.get root = some node)
    (leaves : ∀ i (valid : i < node.children.size), ∃ child,
      tree.nodes.get node.children[i] = some child ∧ child.children = #[])
    (bounded : node.children.size ≤ tree.nodes.size) (i : Nat) (fits : i ≤ node.children.size) :
    Lean.Loop.forIn {} (none,tree,#[(root,i)],2*i) (outerScan tree root live) =
      Lean.Loop.forIn {} (none,tree,#[(root,node.children.size)],2*node.children.size) (outerScan tree root live) := by
  generalize difference : node.children.size-i = remaining
  induction remaining generalizing i with
  | zero =>
    have equal : i = node.children.size := by omega
    rw [equal]
  | succ remaining ih =>
    have inside : i < node.children.size := by omega
    obtain ⟨child,lookup,empty⟩ := leaves i inside
    rw [Lean.Loop.forIn_eq_of_monadTail,descend tree root node live present i inside bounded]
    simp only [bind]
    rw [Lean.Loop.forIn_eq_of_monadTail,leaf tree root node.children[i] child live lookup empty i (by omega)]
    simp only [bind]
    exact ih (i+1) (by omega) (by omega)

/-- The actual root postorder fold completes after all childless descendants
have been visited. The result is the real deletion fold followed by root rewrite. -/
theorem complete (tree : BorrowTree) (root : UniIndex) (node : TreeNode) (live : Array BorTag)
    (present : tree.nodes.get root = some node)
    (distinct : node.children.toList.Nodup) (notChild : root ∉ node.children.toList)
    (leaves : ∀ index ∈ node.children.toList, ∃ child,
      tree.nodes.get index = some child ∧ child.children = #[])
    (bounded : node.children.size ≤ tree.nodes.size) :
    ∃ (after : BorrowTree) (kept : Array UniIndex),
      source_gc_children tree root live =
        ⟨{after with nodes := after.nodes.insert root {node with children := kept}},.ok ()⟩ ∧
      after.nodes.get root = some node ∧ after.nodes.size = tree.nodes.size ∧
      forIn node.children.toList (none,tree,#[]) (childScan tree root live root) = (none,after,kept) := by
  obtain ⟨after,kept,folded,capacity,outside⟩ := GeneralBorrowGcLeafFold.complete
    node.children.toList tree tree root root live #[] distinct leaves
  have rootPresent := (outside root notChild).trans present
  let final := {after with nodes := after.nodes.insert root {node with children := kept}}
  have lastStep : outerScan tree root live () (none,tree,#[(root,node.children.size)],2*node.children.size) =
      .yield (none,final,#[],2*node.children.size+1) := by
    have counter : ¬ tree.nodes.size*2+1 < 2*node.children.size+1 := by omega
    simp only [outerScan,pure]
    simp only [show (!#[(root,node.children.size)].isEmpty) = true from rfl,↓reduceIte,counter]
    simp only [show (#[(root,node.children.size)] : Array (UniIndex × Nat)).back? = some (root,node.children.size) from rfl,present,Nat.lt_irrefl,↓reduceIte]
    fold_gc_child_callback (tree,root,live,root)
    rw [←Array.forIn_toList,folded]
    simp [rootPresent,final,bind,pure]
  have finished : Lean.Loop.forIn {} (none,tree,#[(root,node.children.size)],2*node.children.size)
      (outerScan tree root live) = (none,final,#[],2*node.children.size+1) := by
    rw [Lean.Loop.forIn_eq_of_monadTail,lastStep]
    simp only [bind]
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp [outerScan,bind,pure]
  have visited := visit tree root node live present (fun i valid => leaves node.children[i]
    (Array.mem_toList_iff.mpr (Array.getElem_mem valid))) bounded 0 (by omega)
  refine ⟨after,kept,?_,rootPresent,capacity,folded⟩
  rw [children_equation]
  simp only [Nat.mul_zero] at visited
  rw [visited,finished]



end DuplicatePrefix.GeneralBorrowGcStarWalk
