import Miri.Input.Reader.Catalog
import Miri.Input.DecoderValues
import Miri.Input.CompilerExternAbi

namespace Miri.Input.Reader
open Lean

private def signature (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String Unit := do
  let ty := fun value => do
    let id ← catalog.natural (← catalog.field value "type_id" path) path
    unless id < count do throw s!"{path}: invalid signature type {id}"
  for value in (← catalog.array (← catalog.field input "inputs" path) path) do ty value
  ty (← catalog.field input "output" path)
  let safety ← catalog.field input "safety" path
  catalog.requireSupported safety path
  let kind ← catalog.string (← catalog.field safety "kind" path) path
  unless kind == "safe" || kind == "unsafe" do throw s!"{path}: unknown signature safety"
  let abi ← catalog.field input "abi" path
  catalog.requireSupported abi path
  let unwind ← match ← catalog.optionalField abi "unwind" path with
    | none | some .null => pure none
    | some value => some <$> catalog.boolean value path
  let _ ← CompilerExternAbi.ofFields (← catalog.string (← catalog.field abi "kind" path) path) unwind
  let _ ← catalog.boolean (← catalog.field input "c_variadic" path) path
  pure ()

def Catalog.readTypes (catalog : Catalog) (layoutIds : Array Nat)
    (facts : Array (Option TypeCompilerFacts)) (relations : Array TypeRelations) : Except String (Array TypeNode) := do
  let values ← catalog.array (← catalog.field catalog.root "types" "$") "$.types"
  values.mapIdxM fun index input => do
    let path := s!"$.types[{index}]"
    let shape ← catalog.field input "shape" path
    let optionalText := fun key => do
      match ← catalog.optionalField shape key path with
      | none | some .null => pure none
      | some value => some <$> catalog.string value path
    if let some value ← catalog.optionalField shape "signature" path then
      let value ← catalog.inspect value path
      unless value == .null do signature catalog values.size value path
    let some layoutId := layoutIds[index]? | throw s!"{path}: layout absent"
    let some compilerFacts := facts[index]? | throw s!"{path}: compiler facts absent"
    let some relations := relations[index]? | throw s!"{path}: type relations absent"
    return {
      id := ← catalog.natural (← catalog.field input "type_id" path) path
      display := ← catalog.string (← catalog.field input "display" path) path
      shapeStatus := DecoderValues.parseStatus (← catalog.string (← catalog.field shape "status" path) path)
      shapeKind := DecoderValues.typeShapeKind (← catalog.string (← catalog.field shape "kind" path) path)
      shapeMetadata := {
        signedKind := (← optionalText "signed_kind").map DecoderValues.integerTypeTag
        unsignedKind := (← optionalText "unsigned_kind").map DecoderValues.integerTypeTag
        floatKind := (← optionalText "float_kind").map DecoderValues.floatTypeTag
        adtKind := (← optionalText "adt_kind").map DecoderValues.adtKindTag }
      compilerFacts,layoutId,relations }

end Miri.Input.Reader
