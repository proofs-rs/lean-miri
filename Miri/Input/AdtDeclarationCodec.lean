import Miri.Input.AdtDeclaration
import Miri.Input.ReprMaterialCodec
import Miri.Input.TraitSelection.Codec

namespace Miri.Input.AdtDeclarationCodec
open GenericSubstitution AdtDeclaration

private def keys (value : Lean.Json) (allowed : List String) : Except String Unit := do
  for (key, _) in (← value.getObj?).toArray do
    unless allowed.contains key do throw s!"unknown raw ADT declaration field {key}"

private def optionalIdentity (value : Lean.Json) : Except String (Option DefinitionIdentity) := do
  if value == .null then pure none
  else
    keys value ["definition"]
    pure (some (← GenericMaterialCodec.readDefinition (← value.getObjVal? "definition")))

private def field (value : Lean.Json) : Except String FieldSafety := do
  keys value ["variant", "field", "unsafe", "field_name", "definition", "visibility", "mutation_restriction", "default_value"]
  pure {
    variantIndex := ← (← value.getObjVal? "variant").getNat?
    fieldIndex := ← (← value.getObjVal? "field").getNat?
    isUnsafe := ← (← value.getObjVal? "unsafe").getBool?
    fieldName := ← (← value.getObjVal? "field_name").getStr?
    definition := ← GenericMaterialCodec.readDefinition (← value.getObjVal? "definition")
    visibility := ← optionalIdentity (← value.getObjVal? "visibility")
    mutationRestriction := ← optionalIdentity (← value.getObjVal? "mutation_restriction")
    defaultValue := ← optionalIdentity (← value.getObjVal? "default_value") }

private def variant (value : Lean.Json) : Except String Variant := do
  keys value ["definition", "constructor", "name", "discriminant", "field_count", "flags_bits"]
  let rawConstructor ← value.getObjVal? "constructor"
  let constructor ← if rawConstructor == .null then pure none else do
    keys rawConstructor ["kind", "definition"]
    let kind ← match ← (← rawConstructor.getObjVal? "kind").getStr? with
      | "function" => pure ConstructorKind.function | "constant" => pure .constant
      | _ => throw "unknown raw ADT constructor kind"
    pure (some ⟨kind,← GenericMaterialCodec.readDefinition (← rawConstructor.getObjVal? "definition")⟩)
  let rawDiscriminant ← value.getObjVal? "discriminant"
  let discriminant ← match ← (← rawDiscriminant.getObjVal? "kind").getStr? with
    | "relative" =>
      keys rawDiscriminant ["kind", "distance"]
      pure (Discriminant.relative (← (← rawDiscriminant.getObjVal? "distance").getNat?))
    | "explicit" =>
      keys rawDiscriminant ["kind", "definition"]
      pure (Discriminant.explicit (← GenericMaterialCodec.readDefinition (← rawDiscriminant.getObjVal? "definition")))
    | _ => throw "unknown raw ADT discriminant kind"
  pure {
    definition := ← GenericMaterialCodec.readDefinition (← value.getObjVal? "definition")
    constructor, discriminant
    name := ← (← value.getObjVal? "name").getStr?
    fieldCount := ← (← value.getObjVal? "field_count").getNat?
    flagsBits := ← (← value.getObjVal? "flags_bits").getNat? }

def read (template : DefinitionTemplate) (value : Lean.Json) : Except String Material := do
  keys value ["flags_bits", "lang_item", "variants", "fields", "representation", "nonnull_optimization_guaranteed"]
  let rawLang ← value.getObjVal? "lang_item"
  let langItem ← if rawLang == .null then pure none else pure (some (← rawLang.getStr?))
  let material : Material := {
    representation := ← ReprMaterialCodec.read (← value.getObjVal? "representation")
    flagsBits := ← (← value.getObjVal? "flags_bits").getNat?
    langItem
    nonnullOptimizationGuaranteed := ← (← value.getObjVal? "nonnull_optimization_guaranteed").getBool?
    variants := ← (← (← value.getObjVal? "variants").getArr?).mapM variant
    fields := ← (← (← value.getObjVal? "fields").getArr?).mapM field }
  material.validate template
  pure material

end Miri.Input.AdtDeclarationCodec
