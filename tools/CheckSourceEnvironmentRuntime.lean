import Miri.Input.Decoder
import Miri.Input.AliasRuntime

/-! Fresh producer/consumer control for execution-local source impl obligations.
The fixture is tests/repro/compiler-queries/source-environment.rs. Removed
legacy predicate fields must reject at the wire boundary; removing the
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
  let raw ← require (Lean.Json.parse (← IO.FS.readFile path))
  let program ← require (raw.getObjVal? "compiler_trait_program")
  let traits ← require ((← require (program.getObjVal? "traits")).getArr?)
  let poisonedTraits ← traits.mapM fun declaration => do
    let implementations ← require ((← require (declaration.getObjVal? "implementations")).getArr?)
    pure (declaration.setObjVal! "implementations" (.arr (implementations.map fun implementation =>
      implementation.setObjVal! "predicates" (.arr #[]))))
  let poisoned := raw.setObjVal! "compiler_trait_program" (program.setObjVal! "traits" (.arr poisonedTraits))
  match decodeJson poisoned.compress with
  | .ok _ => throw (IO.userError "removed copied predicate field was accepted")
  | .error error =>
    unless error.endsWith "unknown raw trait material field predicates" do
      throw (IO.userError s!"unexpected legacy predicate rejection: {error}")
  let absent := {document with definitions := document.definitions.map fun definition =>
    if (⟨definition.crateIndex,definition.index⟩ : DefinitionIdentity) == selection.implementation
    then {definition with sourceEnvironment := none} else definition}
  let context ← require (AliasRuntime.Context.ofDocument absent)
  match AliasRuntime.selectGoal context 256 100000 goal with
  | .ok _ => throw (IO.userError "selected impl succeeded without its source obligation scope")
  | .error error =>
    unless error == "raw source environment declaration is absent" do
      throw (IO.userError s!"unexpected missing-scope failure: {error}")
  IO.println "source environment runtime selection PASS: source obligations consumed, removed copied fields rejected, missing source rejected"
