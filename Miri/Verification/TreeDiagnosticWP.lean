import Miri.Input.EvalMiriTreeDiagnostics
import Std.Tactic.Do

/-! Exact ancestor selection and name updates for the concrete Tree Borrows
diagnostic shims. Diagnostic output effects remain inputs to their source
entrypoints. -/
namespace Miri.Verification.TreeDiagnosticWP

open Miri.Memory Miri.TreeBorrows

attribute [spec] Miri.Input.EvalMiriTreeDiagnostics.namePointer
attribute [spec] Miri.Input.EvalMiriTreeDiagnostics.printBorrowState

private def ancestorStep (tree : BorrowTree) (tag : BorTag) (step : Nat) (index : UniIndex) :
    Except DebugNameError (ForInStep UniIndex) := do
  let some node := tree.nodes.get index | throw (.missingNode index)
  let some parent := node.parent | throw (.missingParent tag (step + 1))
  pure (.yield parent)

/-- A malformed or exhausted parent chain reports the earliest failing visit
in the interpreter's ancestor order. -/
def ancestorPre (tree : BorrowTree) (tag : BorTag) (post : BorTag → Prop)
    (failure : DebugNameError → Prop) : List Nat → UniIndex → Prop
  | [], index =>
    match tree.nodes.get index with
    | some node => post node.tag
    | none => failure (.missingNode index)
  | step :: rest, index =>
    match tree.nodes.get index with
    | none => failure (.missingNode index)
    | some node =>
      match node.parent with
      | none => failure (.missingParent tag (step + 1))
      | some parent => ancestorPre tree tag post failure rest parent

private theorem ancestorPre_iff (tree : BorrowTree) (tag : BorTag)
    (post : BorTag → Prop) (failure : DebugNameError → Prop) (steps : List Nat)
    (index : UniIndex) :
    (match (do
      let last ← forIn steps index (ancestorStep tree tag)
      let some node := tree.nodes.get last | throw (.missingNode last)
      pure node.tag : Except DebugNameError BorTag) with
    | .ok result => post result
    | .error error => failure error) ↔ ancestorPre tree tag post failure steps index := by
  induction steps generalizing index with
  | nil =>
    simp only [List.forIn_nil, ancestorPre, bind, Bind.bind, Except.bind,
      pure, Pure.pure, Except.pure]
    cases tree.nodes.get index <;> rfl
  | cons step rest ih =>
    simp only [List.forIn_cons, ancestorStep, ancestorPre]
    cases found : tree.nodes.get index with
    | none =>
      simp only [bind, Bind.bind, Except.bind, throw]
      rfl
    | some node =>
      cases parentEq : node.parent with
      | none =>
        simp only [parentEq, bind, Bind.bind, Except.bind, throw]
        rfl
      | some parent =>
        simp only [parentEq, bind, Bind.bind, Except.bind, pure, Pure.pure, Except.pure]
        exact ih parent

def nthParentPre (tree : BorrowTree) (tag : BorTag) (distance : Nat)
    (post : BorTag → Prop) (failure : DebugNameError → Prop) : Prop :=
  match tree.tagMapping.get tag with
  | none => failure (.missingTag tag)
  | some index => ancestorPre tree tag post failure (List.range' 0 distance) index

theorem nthParentPre_iff (tree : BorrowTree) (tag : BorTag) (distance : Nat)
    (post : BorTag → Prop) (failure : DebugNameError → Prop) :
    (match tree.nthParent tag distance with
    | .ok parent => post parent
    | .error error => failure error) ↔ nthParentPre tree tag distance post failure := by
  unfold BorrowTree.nthParent nthParentPre
  cases tree.tagMapping.get tag with
  | none => rfl
  | some index =>
    dsimp only
    simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    exact ancestorPre_iff tree tag post failure (List.range' 0 distance) index

/-- A name update touches only the selected ancestor, after a successful
ancestor search and relookup of its tag. -/
def namePre (tree : BorrowTree) (tag : BorTag) (distance : Nat) (name : String)
    (post : BorrowTree → Prop) (failure : DebugNameError → Prop) : Prop :=
  nthParentPre tree tag distance (fun ancestor =>
    match tree.tagMapping.get ancestor with
    | none => failure (.missingTag ancestor)
    | some index =>
      match tree.nodes.get index with
      | none => failure (.missingNode index)
      | some node =>
        let debugName := match node.debugName with
          | none => name
          | some existing => existing ++ ", " ++ name
        post { tree with nodes := tree.nodes.insert index { node with debugName := some debugName } })
    failure

theorem namePre_iff (tree : BorrowTree) (tag : BorTag) (distance : Nat) (name : String)
    (post : BorrowTree → Prop) (failure : DebugNameError → Prop) :
    (match tree.givePointerDebugName tag distance name with
    | .ok after => post after
    | .error error => failure error) ↔ namePre tree tag distance name post failure := by
  unfold BorrowTree.givePointerDebugName namePre
  rw [← nthParentPre_iff]
  cases tree.nthParent tag distance with
  | error error => rfl
  | ok ancestor =>
    simp only [bind, Bind.bind, Except.bind]
    unfold BorrowTree.addDebugName
    cases tree.tagMapping.get ancestor with
    | none => rfl
    | some index =>
      dsimp only
      cases tree.nodes.get index <;> rfl

end Miri.Verification.TreeDiagnosticWP
