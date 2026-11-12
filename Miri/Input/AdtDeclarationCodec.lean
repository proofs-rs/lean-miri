import Miri.Input.AdtDeclaration
import Miri.Input.ReprMaterialCodec
import Miri.Input.TraitSelection.Codec

namespace Miri.Input.AdtDeclarationCodec
open GenericSubstitution AdtDeclaration

private def keys (value : Lean.Json) (allowed : List String) : Except String Unit := do
  for (key, _) in (← value.getObj?).toArray do
    unless allowed.contains key do throw s!"unknown raw ADT declaration field {key}"

private def field (value : Lean.Json) : Except String FieldSafety := do
  keys value ["variant", "field", "unsafe", "field_name"]
  pure {
    variantIndex := ← (← value.getObjVal? "variant").getNat?
    fieldIndex := ← (← value.getObjVal? "field").getNat?
    isUnsafe := ← (← value.getObjVal? "unsafe").getBool?
    fieldName := ← (← value.getObjVal? "field_name").getStr? }

def read (template : DefinitionTemplate) (value : Lean.Json) : Except String Material := do
  keys value ["kind", "lang_item", "variant_count", "variant_names", "fields", "representation"]
  let kind ← match ← (← value.getObjVal? "kind").getStr? with
    | "struct" => pure AdtKind.structKind
    | "enum" => pure .enumKind
    | "union" => pure .unionKind
    | _ => throw "unknown raw ADT declaration kind"
  let rawLang ← value.getObjVal? "lang_item"
  let langItem ← if rawLang == .null then pure none else pure (some (← rawLang.getStr?))
  let material : Material := {
    representation := ← ReprMaterialCodec.read (← value.getObjVal? "representation")
    kind
    langItem
    variantCount := ← (← value.getObjVal? "variant_count").getNat?
    variantNames := ← (← (← value.getObjVal? "variant_names").getArr?).mapM (·.getStr?)
    fields := ← (← (← value.getObjVal? "fields").getArr?).mapM field }
  material.validate template
  pure material


end Miri.Input.AdtDeclarationCodec
