import Miri.Input.Decoder
import Miri.Input.AliasRuntime

/-! Independent codegen_select_candidate answers for raw structural auto traits.
Source impl identities/substitutions, builtin selection, and no-solution are
compared separately. Novel goals must have no exact source type-table row. -/
open Lean (Json)
open Miri.Input Miri.Input.GenericSubstitution Miri.Input.TraitSelection
private def require (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [candidatePath, oraclePath] := args
    | throw (IO.userError "usage: CompareStructuralAuto candidate.json oracle.json")
  let input ← require (decodeJson (← IO.FS.readFile candidatePath))
  let source := input.document
  let context ← require (AliasRuntime.Context.ofDocument source)
  let oracle ← require (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← require oracle.getArr?
  let mut implementations := 0
  let mut builtins := 0
  let mut negative := 0
  let mut novel := 0
  let mut cycleBoundaries := 0
  for row in rows do
    let goal ← require (Codec.readTraitRef (← require (row.getObjVal? "goal")))
    if ← require ((← require (row.getObjVal? "novel_goal")).getBool?) then
      let some self := goal.arguments[0]? | throw (IO.userError "novel Self absent")
      for node in source.types do
        let relevant := match node.shape, self with
          | .adt .., .definition .type "adt" .. => true
          | .array .., .node .type "array" .. => true
          | _, _ => false
        if relevant then
          let existing ← require (GenericInstantiation.ofType context.generic 256 node.id)
          if existing = self then throw (IO.userError "novel structural auto-trait goal already occurs in source type table")
      novel := novel + 1
    let expected ← require (row.getObjVal? "expected")
    let kind ← require ((← require (expected.getObjVal? "kind")).getStr?)
    let result ← require (AliasRuntime.solveGoal context 256 20000 ⟨.positive,goal⟩)
    if ← require ((← require (row.getObjVal? "coinductive_boundary")).getBool?) then
      unless kind == "builtin" do throw (IO.userError "coinductive boundary must be rustc-positive")
      match result with
      | .ambiguous _ => cycleBoundaries := cycleBoundaries + 1
      | _ => throw (IO.userError "unported coinductive cycle was not explicit ambiguity")
      continue
    match kind, result with
    | "implementation", .proven (.implementation selected _) =>
      let definition ← require (GenericMaterialCodec.readDefinition (← require (expected.getObjVal? "definition")))
      let rawArguments ← require ((← require (expected.getObjVal? "arguments")).getArr?)
      let arguments ← require (rawArguments.mapM (GenericMaterialCodec.readTerm 4096))
      unless selected.implementation == definition && decide (selected.substitution = arguments) do
        throw (IO.userError "structural auto-trait source impl/substitution mismatch")
      implementations := implementations + 1
    | "builtin", .proven (.builtin _ _) => builtins := builtins + 1
    | "no_solution", .noSolution => negative := negative + 1
    | _, _ => throw (IO.userError s!"structural auto-trait outcome differs: expected {kind}, actual {repr result}")
  unless implementations >= 1 && builtins >= 3 && negative >= 4 && novel >= 2 && cycleBoundaries >= 1 do
    throw (IO.userError "structural auto-trait fixture lost source/builtin/negative/novel branches")
  IO.println s!"structural auto-trait rustc differential PASS: source_impl={implementations}, builtin={builtins}, no_solution={negative}, uninterned_goals={novel}; separate coinductive boundary controls={cycleBoundaries}"
