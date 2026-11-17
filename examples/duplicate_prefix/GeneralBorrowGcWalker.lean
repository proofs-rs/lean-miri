import duplicate_prefix.GeneralBorrowGcAllocator
namespace DuplicatePrefix.GeneralBorrowGcWalker
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open Lean Elab Tactic
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000
elab "source_gc_children" : term => do
  let candidates := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.removeUselessChildren" then some name else none
  match candidates with
  | [name] => return mkConst name
  | _ => throwError "expected unique pinned GC child walker"
elab "unfold_source_gc_children" : tactic => do
  let candidates := (←getEnv).constants.toList.filterMap fun (name,_) =>
    if name.toString.endsWith ".BorrowTree.removeUselessChildren" then some name else none
  match candidates with
  | [name] => let name := mkIdent name;evalTactic (← `(tactic| unfold $name:ident))
  | _ => throwError "expected unique pinned GC child walker"

abbrev ChildState := Option BorrowTree.TreeGcResult × BorrowTree × Array UniIndex
abbrev OuterState := Option BorrowTree.TreeGcResult × BorrowTree × Array (UniIndex × Nat) × Nat

/-- Extract the exact outer callback from the pinned source, retaining its
compiler-generated sparse matches and early-return machinery. The exported
body is a kernel-checked expression; children_equation checks the extraction. -/
elab "source_gc_outer_scan" "(" tree:term "," root:term "," live:term ")" : term => do
  let tree ← Lean.Elab.Term.elabTerm tree (some (mkConst ``BorrowTree))
  let root ← Lean.Elab.Term.elabTerm root (some (mkConst ``UniIndex))
  let live ← Lean.Elab.Term.elabTerm live (some (mkApp (mkConst ``Array [Level.zero]) (mkConst ``BorTag)))
  let candidates := (←getEnv).constants.toList.filterMap fun (name,info) =>
    if name.toString.endsWith ".BorrowTree.removeUselessChildren" then some info else none
  let [info] := candidates | throwError "expected unique source GC walker"
  let expression ← Lean.Meta.zetaReduce (info.value!.beta #[tree,root,live])
  let some loop := expression.find? (fun expression => expression.isAppOf ``ForIn.forIn)
    | throwError "expected source outer forIn"
  return loop.getAppArgs.back!

def outerScan (tree : BorrowTree) (root : UniIndex) (live : Array BorTag) : Unit → OuterState → Id (ForInStep OuterState) :=
  source_gc_outer_scan (tree, root, live)

theorem children_equation (tree : BorrowTree) (root : UniIndex) (live : Array BorTag) :
    source_gc_children tree root live =
      let result := Lean.Loop.forIn {} (none,tree,#[(root,0)],0) (outerScan tree root live)
      match result.1 with
      | some returned => returned
      | none => ⟨result.2.1,.ok ()⟩ := by
  unfold_source_gc_children
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have same : scan = outerScan tree root live := rfl
  rw [same]
  generalize actual : Lean.Loop.forIn {} (none,tree,#[(root,0)],0) (outerScan tree root live) = result
  rcases result with ⟨returned,current,stack,steps⟩
  cases returned <;> rfl
end DuplicatePrefix.GeneralBorrowGcWalker
