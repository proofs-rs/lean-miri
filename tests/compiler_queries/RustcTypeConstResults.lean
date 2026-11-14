import Miri.Input.Decoder
import Miri.Input.RuntimeEffectfulLayout

open Lean Miri Miri.Input Miri.Interpreter GenericSubstitution

private def must [ToString ε] (value : Except ε α) : IO α :=
  match value with
  | .ok result => pure result
  | .error error => throw (IO.userError (toString error))

private structure State where
  types : RuntimeArrayTypes.World

private def arrays : RuntimeArrayQueries.Access State :=
  ⟨(·.types), fun state types => {state with types}⟩

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh rustc export")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let some row := document.compilerTypeConstResults.find? (fun row =>
      row.aliasKind == "anonymous" && !row.rigid && row.genericArgs.isEmpty)
    | throw (IO.userError "fresh export lacks concrete anonymous alias result")
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let world ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let identity ← must (world.arena.identity row.definition)
  let some (.Value expectedType _) := document.typeConstants[row.valueConstId]?
    | throw (IO.userError "result is not a rustc Value")
  let source : GenericSubstitution.Term := .definition .constant "alias_anonymous_not_rigid" identity .nil
  let expected ← must (GenericInstantiationWorld.ofConstant world.arena
    runtime.materialLayoutFuel row.valueConstId)
  let provider := RuntimeEffectfulLayout.compilerResults arrays runtime
  let actual ← match (provider CompilerTypingEnv.fullyMonomorphized expectedType none source).run {types := world} with
    | .ok value _ => pure value
    | .error error _ => throw (IO.userError s!"exact rustc result unavailable: {repr error}")
  unless actual == expected do throw (IO.userError "rustc type constant result changed")
  let missing := {runtime with source := {runtime.source with compilerTypeConstResults := #[]}}
  match (RuntimeEffectfulLayout.compilerResults arrays missing
      CompilerTypingEnv.fullyMonomorphized expectedType none source).run {types := world} with
  | .error _ _ => pure ()
  | .ok _ _ => throw (IO.userError "missing rustc type constant result was accepted")
  IO.println "PASS exact rustc type-level constant result and missing-result rejection"
