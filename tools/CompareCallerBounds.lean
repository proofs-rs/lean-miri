import Miri.Input.SourceEnvironmentRuntime
import Miri.Input.Decoder
import Miri.Input.TraitSelection.EnvironmentEntailment
import Miri.Input.TraitSelection.Fulfill

/-! Positive-only declaration-bound comparison. Rustc-negative Maybe<T:?Sized>
is an explicit unknown boundary of this helper, not a Lean negative proof. -/
open Lean (Json)
open Miri.Input Miri.Input.GenericSubstitution Miri.Input.TraitSelection
private def require (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def rejectingHooks : Hooks := {
  implementationPredicates := fun _ => .error "no raw impl scope supplied",
  normalize := fun _ _ value => .ok value,
  builtin := fun _ _ _ _ => .error "no external builtin supplied",
  external := fun _ _ _ _ => .error "no external predicate supplied" }
def main (args : List String) : IO Unit := do
  let [candidatePath, oraclePath] := args
    | throw (IO.userError "usage: CompareEnvironmentBounds candidate.json oracle.json")
  let input ← require (decodeJson (← IO.FS.readFile candidatePath))
  let source := input.document
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
    let _ ← require (match definition.adtDeclaration with
      | some _ => .ok () | none => .error "source ADT metadata absent")
    let assumptions ← require (SourceEnvironment.predicates (SourceEnvironmentRuntime.lookup source) 256 identity)
    let parameter ← require (GenericMaterialCodec.readTerm 4096 (← require (row.getObjVal? "parameter")))
    let expected ← require ((← require (row.getObjVal? "expected")).getStr?)
    let traitDefinition ← require (GenericMaterialCodec.readDefinition (← require (row.getObjVal? "trait_definition")))
    let goal : Clause := ⟨#[],.trait ⟨.positive,⟨traitDefinition,#[parameter]⟩⟩⟩
    let outcome ← require (solveWithSourceParameters source.traitProgram rejectingHooks
      {assumptions := assumptions} template.parameters 256 2000
      ⟨.positive,⟨traitDefinition,#[parameter]⟩⟩)
    let proof ← match outcome with
      | .proven (.sourceEnvironment proof) => pure (some proof)
      | .ambiguous _ => pure none
      | _ => throw (IO.userError "caller-bound solver returned an unexpected classification")
    if expected == "parameter" then
      unless proof.isSome do throw (IO.userError "source-bound positive entailment differs from rustc")
      match proof with
      | some (.superClause ..) =>
        let withoutSupers := { source.traitProgram with
          traits := source.traitProgram.traits.map fun trait => { trait with superPredicates := #[] } }
        let missing ← require (EnvironmentEntailment.entails withoutSupers template.parameters
          assumptions 256 goal)
        unless missing.isNone do throw (IO.userError "removing raw superclauses retained derived proof")
      | _ => pure ()
      positive := positive + 1
    else
      unless proof.isNone do throw (IO.userError "source-bound helper proved a rustc-negative goal")
      unknownBoundary := unknownBoundary + 1
  unless positive >= 1 && unknownBoundary >= 1 do throw (IO.userError "source bounds fixture lost branches")
  IO.println s!"source caller-bound entailment PASS: {positive} genuine rustc-positive proofs; {unknownBoundary} separately unknown boundary controls"
