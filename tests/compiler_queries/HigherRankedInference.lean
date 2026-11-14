import Miri.Input.TraitSelection.Inference

open Miri.Input.GenericSubstitution Miri.Input.TraitSelection

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

private def placeholder (universeIndex position : Nat) : Term :=
  .placeholder .region universeIndex position .anonymous

private def borrow (region : Term) : Term :=
  .node .type "reference" "immutable" (.ofArray #[region,.atom .type "uint" "u8"])

def main : IO Unit := do
  let action : Inference.M Unit := do
    let oldType ← Inference.fresh .type 0
    let scope ← Inference.freshUniverse
    let recentRegion ← Inference.fresh .region scope.current
    let .inference _ oldId := oldType | throw "old inference constructor"
    let .inference _ recentId := recentRegion | throw "recent inference constructor"
    unless ← Inference.assign 100 oldId (borrow recentRegion) do
      throw "unresolved region could not enter an earlier type assignment"
    let before ← get
    if ← Inference.assign 100 recentId (placeholder scope.current 0) then
      throw "later assignment leaked a placeholder through an older type"
    unless (← get) == before do throw "failed assignment changed inference state"
    unless ← Inference.assign 100 recentId (.atom .region "static" "") do
      throw "static assignment unexpectedly failed"
    let resolved ← match Inference.resolve (← get) 100 oldType with
      | .ok value => pure value | .error error => throw error
    unless resolved == borrow (.atom .region "static" "") do
      throw "transitive assignment resolution lost the static lifetime"
  let _ ← must (action.run {})
  let occurs : Inference.M Unit := do
    let value ← Inference.fresh .type 0
    let .inference _ id := value | throw "type inference constructor"
    if ← Inference.assign 100 id (.node .type "slice" "" (.ofArray #[value])) then
      throw "occurs check admitted an infinite type"
    if ← Inference.assign 100 id (.atom .region "static" "") then
      throw "assignment admitted another generic sort"
    unless ← Inference.assign 100 id value do throw "reflexive assignment failed"
  let _ ← must (occurs.run {})
  let freshBinder : Inference.M Unit := do
    let scope ← Inference.freshUniverse
    let term ← Inference.instantiateBinder scope.current 100 #[.region .anonymous]
      (.binder #[.region .anonymous] (.node .type "tuple" "" (.ofArray #[
        .bound .region (.Bound 0) 0 .anonymous,
        .bound .region (.Bound 1) 0 .anonymous,
        .bound .region (.Bound 2) 0 .anonymous])))
    let expected : Term := .binder #[.region .anonymous] (.node .type "tuple" "" (.ofArray #[
      .bound .region (.Bound 0) 0 .anonymous,
      .inference .region 0,
      .bound .region (.Bound 1) 0 .anonymous]))
    unless term == expected do throw "existential binder opening lost nested ownership or outward shift"
  let _ ← must (freshBinder.run {})
  let outlives : Inference.M Unit := do
    let scope ← Inference.freshUniverse
    Inference.constrainOutlives (.atom .region "static" "") (placeholder scope.current 0)
  let (_,allowed) ← must (outlives.run {})
  let _ ← must (Inference.checkLeaks allowed 0 100)
  let forbidden : Inference.M Unit := do
    let scope ← Inference.freshUniverse
    Inference.constrainOutlives (placeholder scope.current 0) (.atom .region "static" "")
  let (_,bad) ← must (forbidden.run {})
  check (!(Inference.checkLeaks bad 0 100).isOk) "placeholder-to-static leak was accepted"
  check (!(Inference.resolve {} 0 (.atom .type "bool" "")).isOk) "resolution exhaustion returned a value"
  check (!(Inference.resolve {} 100 (.inference .type 10)).isOk) "unknown inference identity was accepted"
  IO.println "PASS query-local inference, transitive universe visibility, occurs/sort checks, nested binders and directional leaks"
