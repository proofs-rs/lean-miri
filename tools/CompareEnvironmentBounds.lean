import Miri.Input.Decoder
import Miri.Input.TraitSelection.EnvironmentEntailment

/-! Positive-only declaration-bound comparison. Rustc-negative Maybe<T:?Sized>
is an explicit unknown boundary of this helper, not a Lean negative proof. -/
open Lean (Json)
open Miri.Input Miri.Input.GenericSubstitution Miri.Input.TraitSelection
private def require (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
  let [candidatePath, oraclePath] := args
    | throw (IO.userError "usage: CompareEnvironmentBounds candidate.json oracle.json")
  let input ← require (decodeJson (← IO.FS.readFile candidatePath))
  let source := input.document
  let matching := source.traitProgram.traits.filter (·.langItem == some "sized")
  unless matching.size == 1 do throw (IO.userError "Sized source declaration missing or ambiguous")
  let some sized := matching[0]? | throw (IO.userError "Sized source declaration absent")
  let oracle ← require (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← require oracle.getArr?
  let mut positive := 0
  let mut unknownBoundary := 0
  for row in rows do
    let identity ← require (GenericMaterialCodec.readDefinition (← require (row.getObjVal? "definition")))
    let definitions := source.definitions.filter fun definition =>
      definition.crateIndex == identity.crateIndex && definition.index == identity.index
    unless definitions.size == 1 do throw (IO.userError "source ADT declaration missing or ambiguous")
    let some definition := definitions[0]? | throw (IO.userError "source ADT declaration absent")
    let some template := definition.genericTemplate | throw (IO.userError "source ADT template absent")
    let some material := definition.adtDeclaration | throw (IO.userError "source ADT metadata absent")
    let parameter ← require (GenericMaterialCodec.readTerm 4096 (← require (row.getObjVal? "parameter")))
    let expected ← require ((← require (row.getObjVal? "sized")).getBool?)
    let goal : Clause := ⟨#[],.trait ⟨.positive,⟨sized.definition,#[parameter]⟩⟩⟩
    let proof ← require (EnvironmentEntailment.entails source.traitProgram template.parameters
      material.ownPredicates 256 goal)
    if expected then
      unless proof.isSome do throw (IO.userError "source-bound positive entailment differs from rustc")
      match proof with
      | some (.superClause ..) =>
        let withoutSupers := { source.traitProgram with
          traits := source.traitProgram.traits.map fun trait => { trait with superPredicates := #[] } }
        let missing ← require (EnvironmentEntailment.entails withoutSupers template.parameters
          material.ownPredicates 256 goal)
        unless missing.isNone do throw (IO.userError "removing raw superclauses retained derived proof")
      | _ => pure ()
      positive := positive + 1
    else
      unless proof.isNone do throw (IO.userError "source-bound helper proved a rustc-negative goal")
      unknownBoundary := unknownBoundary + 1
  unless positive >= 2 && unknownBoundary >= 1 do throw (IO.userError "source bounds fixture lost branches")
  IO.println s!"source environment entailment PASS: {positive} genuine rustc-positive proofs; {unknownBoundary} separately unknown boundary controls"
