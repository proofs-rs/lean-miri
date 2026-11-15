import Miri.Frontend.Foundation

/-! Finite declaration evidence for the pinned DynMetadata representation.
The std path normalizes Pointee::Metadata to DynMetadata<dyn Trait>; this
validator checks the actual source wrapper chain before using its nonnull AS0
scalar representation. No compiler layout or vtable answer is accepted. -/
namespace Miri.Frontend.Foundation
open Lean

private def definition (d : Document) (j : Json) (key kind : String) : Except String Unit := do
  let id ← j.getObjValAs? Nat key
  let some row := d.definitions[id]? | throw "dyn metadata declaration absent"
  unless (← row.getObjValAs? String "kind") == kind do throw "dyn metadata declaration category mismatch"

private def representation (j : Json) (flags : Nat) : Except String Unit := do
  let r ← j.getObjVal? "repr"
  unless (← r.getObjValAs? Nat "flags_bits") == flags &&
      (← r.getObjVal? "align_bytes") == Json.null &&
      (← r.getObjVal? "pack_bytes") == Json.null &&
      (← r.getObjVal? "integer") == Json.null &&
      (← r.getObjVal? "scalable_element") == Json.null do
    throw "unsupported dyn metadata declaration repr"

/-- Validate captured language-item declarations. The compiler has a structural
fallback when metadata_type is absent, but this finite bridge does not yet
support that domain; absence is retained and rejected rather than inferred. -/
def validateDynMetadataSource (d : Document) : Except String Unit := do
  let source ← d.source.getObjVal? "dyn_metadata_source"
  match ← source.getObjValAs? String "mode" with
  | "metadata_lang_item_absent" =>
    throw "dyn pointer metadata language-item source is unavailable"
  | "lang_item_declarations" =>
    definition d source "metadata_type" "AssocTy"
    definition d source "pointee_trait" "Trait"
    unless (← source.getObjValAs? Nat "metadata_parent") == (← source.getObjValAs? Nat "pointee_trait") do
      throw "metadata associated item parent disagrees with Pointee lang item"
    unless (← source.getObjValAs? Nat "pointee_parameter_count") == 1 &&
        (← source.getObjValAs? Nat "metadata_parameter_count") == 1 do
      throw "unsupported Pointee metadata parameter source"
    let metadata ← source.getObjVal? "dyn_metadata"
    definition d metadata "definition" "Struct"
    representation metadata 0
    unless (← metadata.getObjValAs? Nat "field_count") == 2 &&
        (← metadata.getObjValAs? Nat "parameter_count") == 1 &&
        (← metadata.getObjValAs? Nat "vtable_field") == 0 &&
        (← metadata.getObjValAs? Nat "phantom_field") == 1 do
      throw "unsupported DynMetadata field source"
    let nonnull ← source.getObjVal? "non_null"
    definition d nonnull "definition" "Struct"
    representation nonnull 4
    unless (← nonnull.getObjValAs? String "lang_item") == "non_null" &&
        (← nonnull.getObjValAs? Nat "field_count") == 1 &&
        (← nonnull.getObjValAs? Nat "argument_count") == 1 do throw "unsupported NonNull declaration"
    let field ← nonnull.getObjVal? "field"
    definition d field "pointee_definition" "ForeignTy"
    unless (← field.getObjValAs? String "kind") == "pattern" &&
        (← field.getObjValAs? String "pattern") == "not_null" &&
        (← field.getObjValAs? String "base_kind") == "raw_pointer" &&
        !(← field.getObjValAs? Bool "mutable") &&
        (← field.getObjValAs? String "pointee_kind") == "foreign" do
      throw "unsupported NonNull vtable field source"
    let phantom ← source.getObjVal? "phantom_data"
    definition d phantom "definition" "Struct"
    representation phantom 0
    unless (← phantom.getObjValAs? String "lang_item") == "phantom_data" &&
        (← phantom.getObjValAs? Nat "field_count") == 0 &&
        (← phantom.getObjValAs? Nat "argument_count") == 1 do throw "unsupported PhantomData declaration"
    let argument ← phantom.getObjVal? "argument"
    unless (← argument.getObjValAs? String "kind") == "param" &&
        (← argument.getObjValAs? Nat "index") == 0 do throw "unsupported metadata phantom parameter"
  | _ => throw "dyn metadata source evidence unavailable"

/-- Pointer representation needs source metadata evidence; a bare unsized dyn
layout does not. This traversal is conservative over the demanded type tree. -/
def requiresDynMetadata (ty : ConcreteType) : Except String Bool := go 1024 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String Bool := do
    let .succ fuel := fuel | throw "dyn metadata traversal exhausted"
    match ty with
    | .primitive .. => return false
    | .closure _ arguments => return (← arguments.mapM (go fuel)).any id
    | .nominal _ _ => throw "nominal component requires document physical query"
    | .patternNotNull _ => throw "general constrained-pattern metadata unsupported"
    | .array element _ => go fuel element
    | .tuple fields => return (← fields.mapM (go fuel)).any id
    | .pointer _ (.dynamicObject _) => return true
    | .pointer _ pointee => go fuel pointee
    | .functionPointer inputs output .. => return (← go fuel output) || (← inputs.mapM (go fuel)).any id
    | .dynamicObject source =>
      let args ← source.arguments.mapM (go fuel)
      let projections ← source.projections.mapM fun p => do
        return (← go fuel p.term) || (← p.arguments.mapM (go fuel)).any id
      return args.any id || projections.any id

end Miri.Frontend.Foundation
