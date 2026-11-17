import duplicate_prefix.GeneralBorrowGcWalker
namespace DuplicatePrefix.GeneralBorrowGcChildFold
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
open DuplicatePrefix.GeneralBorrowGcWalker

/-- Extract the production inner callback. The only loose source binding used
by this callback is its enclosing parent index; typechecking rejects changes
that would capture another source value of a different type. -/
elab "source_gc_inner_scan" "(" tree:term "," root:term "," live:term "," parent:term ")" : term => do
  let tree ← Lean.Elab.Term.elabTerm tree (some (mkConst ``BorrowTree))
  let root ← Lean.Elab.Term.elabTerm root (some (mkConst ``UniIndex))
  let live ← Lean.Elab.Term.elabTerm live (some (mkApp (mkConst ``Array [Level.zero]) (mkConst ``BorTag)))
  let parent ← Lean.Elab.Term.elabTerm parent (some (mkConst ``UniIndex))
  let candidates := (←getEnv).constants.toList.filterMap fun (name,info) =>
    if name.toString.endsWith ".BorrowTree.removeUselessChildren" then some info else none
  let [info] := candidates | throwError "expected unique source GC walker"
  let expression ← Lean.Meta.zetaReduce (info.value!.beta #[tree,root,live])
  let some outer := expression.find? (fun expression => expression.isAppOf ``ForIn.forIn)
    | throwError "expected outer source loop"
  let some inner := outer.getAppArgs.back!.find? (fun expression => expression.isAppOf ``ForIn.forIn)
    | throwError "expected inner source loop"
  let callback := inner.getAppArgs.back!
  return callback.instantiateRev (Array.replicate callback.looseBVarRange parent)

def childScan (seed : BorrowTree) (root : UniIndex) (live : Array BorTag) (parent : UniIndex) :
    UniIndex → ChildState → Id (ForInStep ChildState) := source_gc_inner_scan (seed,root,live,parent)

def Good (P : BorrowTree → Prop) (state : ChildState) : Prop :=
  P state.2.1 ∧ ∀ result, state.1 = some result → P result.tree

theorem step_preserves (P : BorrowTree → Prop)
    (removed : ∀ tree index, P tree → P (source_remove_useless_node tree index).1)
    (updated : ∀ tree index oldNode newNode, tree.nodes.get index = some oldNode → newNode.tag = oldNode.tag →
      P tree → P {tree with nodes := tree.nodes.insert index newNode})
    (seed : BorrowTree) (root : UniIndex) (live : Array BorTag) (parent child : UniIndex)
    (state : ChildState) (good : Good P state) : Good P (childScan seed root live parent child state).value := by
  rcases state with ⟨returned,current,kept⟩
  simp only [childScan,pure]
  split
  · have next := removed current child good.1
    split <;> exact ⟨next,by intro result same;cases same <;> exact next⟩
  · split
    · exact ⟨good.1,by intro result same;cases same⟩
    · rename_i replacement found
      have next := removed current child good.1
      split
      · exact ⟨next,by intro result same;cases same <;> exact next⟩
      · split
        · rename_i node present
          have changed := updated (source_remove_useless_node current child).1 replacement node
            {node with parent := some parent} present rfl next
          exact ⟨changed,by intro result same;cases same⟩
        · exact ⟨next,by intro result same;cases same <;> exact next⟩

/-- The exact production child fold preserves any predicate stable under the
actual deletion primitive and tag-preserving node updates, including every
early error prefix. This is a data invariant, not operation-success input. -/
theorem fold_preserves (P : BorrowTree → Prop)
    (removed : ∀ tree index, P tree → P (source_remove_useless_node tree index).1)
    (updated : ∀ tree index oldNode newNode, tree.nodes.get index = some oldNode → newNode.tag = oldNode.tag →
      P tree → P {tree with nodes := tree.nodes.insert index newNode})
    (seed : BorrowTree) (root : UniIndex) (live : Array BorTag) (parent : UniIndex)
    (items : Array UniIndex) (state : ChildState) (good : Good P state) :
    Good P (forIn (m := Id) items state (childScan seed root live parent)) := by
  rw [←Array.forIn_toList]
  apply GeneralBorrowLoop.list_invariant items.toList (childScan seed root live parent) (Good P)
  · intro child member current valid
    exact step_preserves P removed updated seed root live parent child current valid
  · exact good

end DuplicatePrefix.GeneralBorrowGcChildFold
