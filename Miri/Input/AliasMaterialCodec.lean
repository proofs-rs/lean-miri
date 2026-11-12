import Miri.Input.AliasMaterial
import Miri.Input.GenericMaterialCodec
import Miri.Input.TraitSelection.Codec

namespace Miri.Input.AliasMaterialCodec
open Lean GenericSubstitution AliasMaterial

/-- The shared trait codec is mandatory: no source predicates may be dropped or
replaced by successful placeholder obligations while reading alias material. -/
def readDeclarationWith (readClause : Json → Except String TraitSelection.Clause)
    (value : Json) : Except String Declaration := do
  let sourceKind ← (← value.getObjVal? "kind").getStr?
  let allowed := if sourceKind == "free" then
      ["definition", "kind", "has_value", "own_predicates"]
    else ["definition", "kind", "has_value", "own_predicates", "parent",
      "parent_parameter_count", "is_final", "container", "trait_item"]
  for (key, _) in (← value.getObj?).toArray do
    unless allowed.contains key do throw s!"unknown source alias declaration field {key}"
  let definition ← GenericMaterialCodec.readDefinition (← value.getObjVal? "definition")
  let hasValue ← (← value.getObjVal? "has_value").getBool?
  let kind ← match sourceKind with
    | "free" => pure Kind.free
    | "associated" => do
      let parent ← GenericMaterialCodec.readDefinition (← value.getObjVal? "parent")
      let count ← (← value.getObjVal? "parent_parameter_count").getNat?
      let isFinal ← (← value.getObjVal? "is_final").getBool?
      let container ← match ← (← value.getObjVal? "container").getStr? with
        | "trait" => pure Container.trait
        | "inherent_impl" => pure Container.inherentImpl
        | "trait_impl" => do
          let item ← GenericMaterialCodec.readDefinition (← value.getObjVal? "trait_item")
          pure (Container.traitImpl item)
        | _ => throw "unknown associated type container"
      pure (.associated container parent count isFinal)
    | _ => throw "unknown source alias declaration kind"
  let ownPredicates ← (← (← value.getObjVal? "own_predicates").getArr?).mapM readClause
  pure ⟨definition, kind, hasValue, ownPredicates⟩

def readDeclaration (value : Json) : Except String Declaration :=
  readDeclarationWith TraitSelection.Codec.readClause value

def decodeDeclaration : JsonReader.Parser Declaration := do
  JsonReader.liftExcept (readDeclaration (← Lean.Json.Parser.anyCore))

end Miri.Input.AliasMaterialCodec
