import Miri.Input.Decoder
import Miri.Input.AliasRuntime

/-! Fresh producer/consumer control for execution-local source impl obligations.
The fixture is tests/repro/compiler-queries/source-environment.rs. Poisoning the
legacy impl predicate copy must not affect source-driven selection; removing the
actual declaration scope must reject the same matched candidate. -/
open Miri.Input Miri.Input.GenericSubstitution Miri.Input.TraitSelection
private def require (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def named (document : ImportDocument) (name : String) : Except String DefinitionIdentity := do
  let candidates := document.definitions.filter fun definition =>
    definition.crateIndex == 0 && definition.rawPath.any (fun path =>
      path.components.back?.any (·.name == some name))
  unless candidates.size == 1 do throw s!"source fixture name missing/ambiguous: {name}"
  let some definition := candidates[0]? | throw "source fixture definition disappeared"
  pure ⟨definition.crateIndex,definition.index⟩

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "usage: CheckSourceEnvironmentRuntime input.json")
  let input ← require (← decodeFile path)
  let document := input.document
  let wrapper ← require (named document "Wrapper")
  let families := document.traitProgram.traits.filter fun (declaration : TraitDeclaration) =>
    declaration.definition.crateIndex == 0 && declaration.implementations.any fun (implementation : Impl) =>
      match (implementation.traitRef.arguments[0]? : Option Term) with
      | some (Term.definition ArgSort.type "adt" identity _) => identity == wrapper
      | _ => false
  unless families.size == 1 do throw (IO.userError "fixture family trait missing/ambiguous")
  let some family := families[0]? | throw (IO.userError "fixture family trait disappeared")
  let family := family.definition
  let u8 := Term.atom .type "uint" "u8"
  let goal : TraitRef := ⟨family,#[.definition .type "adt" wrapper (.ofArray #[u8]),u8]⟩
  let context ← require (AliasRuntime.Context.ofDocument document)
  let selection ← require (AliasRuntime.selectGoal context 256 100000 goal)
  let poisoned := {document with traitProgram := {document.traitProgram with
    traits := document.traitProgram.traits.map fun declaration => {declaration with
      implementations := declaration.implementations.map fun implementation => {implementation with
        predicates := #[⟨#[],.unstableFeature "must-not-be-read"⟩]}}}}
  let context ← require (AliasRuntime.Context.ofDocument poisoned)
  let actual ← require (AliasRuntime.selectGoal context 256 100000 goal)
  unless actual == selection do throw (IO.userError "selection read copied impl obligations")
  let absent := {poisoned with definitions := poisoned.definitions.map fun definition =>
    if (⟨definition.crateIndex,definition.index⟩ : DefinitionIdentity) == selection.implementation
    then {definition with sourceEnvironment := none} else definition}
  let context ← require (AliasRuntime.Context.ofDocument absent)
  match AliasRuntime.selectGoal context 256 100000 goal with
  | .ok _ => throw (IO.userError "selected impl succeeded without its source obligation scope")
  | .error error =>
    unless error == "raw source environment declaration is absent" do
      throw (IO.userError s!"unexpected missing-scope failure: {error}")
  IO.println "source environment runtime selection PASS: source obligations consumed, copied answers ignored, missing source rejected"
