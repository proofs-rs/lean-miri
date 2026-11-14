import Miri.Input.SourceEnvironmentCodec
import Miri.Input.SourceEnvironment

/-! Compare source-explicit parent inheritance plus Lean's trait self-clause
against pinned `clauses_of(...).instantiate_identity`. The fixture has no
inferred-outlives contribution. This does not claim general ParamEnv support. -/
open Lean (Json)
open Miri.Input Miri.Input.GenericSubstitution Miri.Input.TraitSelection
private def require (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [oraclePath] := args | throw (IO.userError "usage: CompareSourceEnvironment oracle.json")
  let rows ← require ((← require (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  let mut sources : Array (DefinitionIdentity × SourceEnvironment.Material) := #[]
  for row in rows do
    let definition ← require (GenericMaterialCodec.readDefinition (← require (row.getObjVal? "definition")))
    let material ← require (SourceEnvironmentCodec.read (← require (row.getObjVal? "source")))
    if sources.any (fun prior => prior.1 == definition) then throw (IO.userError "duplicate source scope")
    sources := sources.push (definition,material)
  let lookup : SourceEnvironment.Lookup := fun definition => do
    let some (_,material) := sources.find? (·.1 == definition) | throw "source parent scope absent"
    pure material
  let mut labels : Array String := #[]
  let mut inherited := 0
  let mut selfTraits := 0
  for row in rows do
    let definition ← require (GenericMaterialCodec.readDefinition (← require (row.getObjVal? "definition")))
    let label ← require ((← require (row.getObjVal? "label")).getStr?)
    labels := labels.push label
    let actual ← require (SourceEnvironment.predicates lookup 256 definition)
    let expected ← require (Codec.readClauses (← require (row.getObjVal? "expected")))
    unless decide (actual = expected) do throw (IO.userError s!"source predicate inheritance differs for {label}")
    let source ← require (lookup definition)
    if source.parent.isSome then inherited := inherited + 1
    if source.isTrait then selfTraits := selfTraits + 1
  unless labels.size == 5 && ["trait","impl","ordinary","trait_method","impl_method"].all labels.contains
      && inherited == 2 && selfTraits == 1 do
    throw (IO.userError "source scope fixture lost trait/impl/function/parent branches")
  IO.println s!"source predicate inheritance rustc differential PASS: {labels.size} declarations, {inherited} inherited method scopes, {selfTraits} reconstructed trait self-clause"
