import Miri.Input.Decoder
import Miri.Input.AliasRuntime

/-! Genuine rustc codegen_select_candidate differential for a fresh producer
artifact. Seven in-scope goals compare actual selected source impl/substitution or
no-solution, including an uninterned ADT instantiation. An additional rustc-positive outside-scope goal must be rejected
explicitly; this control is not counted as compiler correspondence. -/
open Lean Miri.Input Miri.Input.GenericSubstitution Miri.Input.TraitSelection

private def require (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError error)

private def checkScopeError (value : Except String α) : IO Unit := do
  match value with
  | .error error => unless error == "trait query ADT constructor outside closed source declaration scope" do
      throw (IO.userError s!"unexpected scope failure: {error}")
  | .ok _ => throw (IO.userError "outside-scope query was accepted")

def main (args : List String) : IO Unit := do
  let [candidatePath, oraclePath] := args
    | throw (IO.userError "usage: CompareTraitSelection candidate.json rustc-oracle.json")
  let input ← require (decodeJson (← IO.FS.readFile candidatePath))
  let source := input.document
  let context ← require (AliasRuntime.Context.ofDocument source)
  unless source.traitProgram.constructorScope.isSome do
    throw (IO.userError "fresh producer must declare constructor scope")
  let rawOracle ← require (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← require rawOracle.getArr?
  let mut positive := 0
  let mut negative := 0
  let mut scopeControls := 0
  let mut novelControls := 0
  for row in rows do
    let goal ← require (Codec.readTraitRef (← require (row.getObjVal? "goal")))
    let outside ← require ((← require (row.getObjVal? "outside_scope")).getBool?)
    let novel ← require ((← require (row.getObjVal? "novel_goal")).getBool?)
    if novel then
      let some self := goal.arguments[0]? | throw (IO.userError "novel Self absent")
      for node in source.types do
        if let .adt .. := node.shape then
          let existing ← require (GenericInstantiation.ofType context.generic 128 node.id)
          if existing = self then throw (IO.userError "novel solver goal already exists in exported type table")
      novelControls := novelControls + 1
    let expected ← require (row.getObjVal? "expected")
    let kind ← require ((← require (expected.getObjVal? "kind")).getStr?)
    if outside then
      unless kind == "implementation" do throw (IO.userError "scope control must be rustc-positive")
      checkScopeError (AliasRuntime.solveGoal context 128 10000 ⟨.positive,goal⟩)
      checkScopeError (AliasRuntime.selectGoal context 128 10000 goal)
      scopeControls := scopeControls + 1
      continue
    let actual ← require (AliasRuntime.solveGoal context 128 10000 ⟨.positive,goal⟩)
    match kind, actual with
    | "implementation", .proven _ =>
      let selected ← require (AliasRuntime.selectGoal context 128 10000 goal)
      let definition ← require (GenericMaterialCodec.readDefinition (← require (expected.getObjVal? "definition")))
      let rawArguments ← require (expected.getObjVal? "arguments")
      let argumentArray ← require rawArguments.getArr?
      let arguments ← require (argumentArray.mapM (GenericMaterialCodec.readTerm 4096))
      unless selected.implementation == definition && decide (selected.substitution = arguments) do
        throw (IO.userError "selected source impl/substitution differs from rustc")
      positive := positive + 1
    | "no_solution", .noSolution => negative := negative + 1
    | _, _ => throw (IO.userError s!"trait outcome differs from rustc: expected={kind}, actual={repr actual}")
  unless positive >= 4 && negative >= 3 && scopeControls >= 1 && novelControls >= 1 do
    throw (IO.userError "trait oracle fixture lost positive/negative/scope branches")
  IO.println s!"raw trait selection: {positive} selected impl/substitution + {negative} no-solution rustc comparisons PASS; {scopeControls} outside-scope explicit-rejection + {novelControls} uninterned ADT goal controls PASS"
