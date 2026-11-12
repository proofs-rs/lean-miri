import Miri.Input.Decoder
import Miri.Input.AliasRuntime

/-! Independent codegen_select_candidate answers for both Copy and Clone.
Source impl identities/substitutions, builtin selection, and no-solution are
compared separately. Novel goals must have no exact source type-table row. -/
open Lean (Json)
open Miri.Input Miri.Input.GenericSubstitution Miri.Input.TraitSelection
private def require (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)

private def terms : Terms → Array Term
  | .nil => #[]
  | .cons head tail => #[head] ++ terms tail

/-- Existing FnPtr source lacks the splatted-header reconstruction used by GI.
To prove absence, use only the necessary input/output identity condition. If an
interface could match, fail rather than inventing its missing header. -/
private def excludeFunctionPointer (context : GenericInstantiation.Context)
    (signature : FunctionSignature) (wanted : Term) : IO Unit := do
  let .node .type "function_pointer" _ (.cons (.binder _ (.node .aggregate "signature" _ wantedTypes)) .nil) := wanted
    | throw (IO.userError "novel FnPtr goal has malformed source signature")
  let wantedTypes := terms wantedTypes
  let ids := signature.inputs.push signature.output
  if ids.size != wantedTypes.size then return
  let mut different := false
  for (id, wantedType) in ids.zip wantedTypes do
    let node ← require (TypeArena.node context.types id)
    if !GenericInstantiation.mayMatch context node wantedType then different := true
    else
      let actual ← require (GenericInstantiation.ofType context 256 id)
      if actual != wantedType then different := true
  unless different do
    throw (IO.userError "cannot establish novel FnPtr absence: an existing source interface matches")

def main (args : List String) : IO Unit := do
  let [candidatePath, oraclePath] := args
    | throw (IO.userError "usage: CompareCopyClone candidate.json oracle.json")
  let input ← require (decodeJson (← IO.FS.readFile candidatePath))
  let source := input.document
  let context ← require (AliasRuntime.Context.ofDocument source)
  let oracle ← require (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← require oracle.getArr?
  let mut implementations := 0
  let mut builtins := 0
  let mut negative := 0
  let mut novel := 0
  for row in rows do
    let goal ← require (Codec.readTraitRef (← require (row.getObjVal? "goal")))
    if ← require ((← require (row.getObjVal? "novel_goal")).getBool?) then
      let some self := goal.arguments[0]? | throw (IO.userError "novel Self absent")
      for node in source.types do
        let relevant := match node.shape, self with
          | .adt .., .definition .type "adt" .. => true
          | .functionDefinition .., .definition .type "function_definition" .. => true
          | .functionPointer .., .node .type "function_pointer" .. => true
          | _, _ => false
        if relevant then
          if let .functionPointer signature _ := node.shape then
            excludeFunctionPointer context.generic signature self
          else
            let existing ← require (GenericInstantiation.ofType context.generic 256 node.id)
            if existing = self then throw (IO.userError "novel Copy/Clone goal already occurs in source type table")
      novel := novel + 1
    let expected ← require (row.getObjVal? "expected")
    let kind ← require ((← require (expected.getObjVal? "kind")).getStr?)
    let result ← require (AliasRuntime.solveGoal context 256 20000 ⟨.positive,goal⟩)
    match kind, result with
    | "implementation", .proven (.implementation selected _) =>
      let definition ← require (GenericMaterialCodec.readDefinition (← require (expected.getObjVal? "definition")))
      let rawArguments ← require ((← require (expected.getObjVal? "arguments")).getArr?)
      let arguments ← require (rawArguments.mapM (GenericMaterialCodec.readTerm 4096))
      unless selected.implementation == definition && decide (selected.substitution = arguments) do
        throw (IO.userError "Copy/Clone source impl/substitution mismatch")
      implementations := implementations + 1
    | "builtin", .proven (.builtin _ _) => builtins := builtins + 1
    | "no_solution", .noSolution => negative := negative + 1
    | _, _ => throw (IO.userError s!"Copy/Clone outcome differs: expected {kind}, actual {repr result}")
  unless implementations >= 6 && builtins >= 6 && negative >= 6 && novel >= 6 do
    throw (IO.userError "Copy/Clone fixture lost source/builtin/negative/novel branches")
  IO.println s!"Copy/Clone rustc differential PASS: source_impl={implementations}, builtin={builtins}, no_solution={negative}, uninterned_goals={novel}"
