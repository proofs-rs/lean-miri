import Miri.Input.Reader.Table
import Miri.Input.DecoderValues

namespace Miri.Input.Reader.TypeRelationsReader
open Lean Miri.MIR

abbrev Decode := StateT TypeRelationTables (Except String)

private def typeId (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String Nat := do
  let id ← catalog.natural (← catalog.field input "type_id" path) path
  unless id < count do throw s!"{path}: invalid type ID {id}"
  return id

private def typeList (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.typeLists) (fun state table => {state with typeLists := table})
    (fun input path => do
      let values ← catalog.array input path
      values.mapIdxM fun index value => typeId catalog count value s!"{path}[{index}]") input path

private def field (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.fields) (fun state table => {state with fields := table})
    (fun input path => do return {
      index := ← catalog.natural (← catalog.field input "index" path) path
      name := ← catalog.string (← catalog.field input "name" path) path
      typeId := ← typeId catalog count (← catalog.field input "type" path) path }) input path

private def fields (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.fieldLists) (fun state table => {state with fieldLists := table})
    (fun input path => do
      let values ← catalog.array input path
      let mut result := #[]
      for (value, index) in values.toList.zipIdx do
        let id ← field catalog count value s!"{path}[{index}]"
        let value ← (← get).fields.lookup id |>.mapError (fun id => s!"invalid type field {id}")
        unless value.index == index do throw s!"{path}: field index differs from position"
        result := result.push id
      return result) input path

private def variant (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.variants) (fun state table => {state with variants := table})
    (fun input path => do return {
      index := ← catalog.natural (← catalog.field input "index" path) path
      name := ← catalog.string (← catalog.field input "name" path) path
      fields := ← fields catalog count (← catalog.field input "fields" path) path }) input path

private def variants (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.variantLists) (fun state table => {state with variantLists := table})
    (fun input path => do
      let values ← catalog.array input path
      let mut result := #[]
      for (value, index) in values.toList.zipIdx do
        let id ← variant catalog count value s!"{path}[{index}]"
        let value ← (← get).variants.lookup id |>.mapError (fun id => s!"invalid type variant {id}")
        unless value.index == index do throw s!"{path}: variant index differs from position"
        result := result.push id
      return result) input path

private def nullable (catalog : Catalog) (input : Json) (key path : String) : Except String (Option Json) := do
  let value ← catalog.inspect (← catalog.field input key path) path
  return if value == .null then none else some value

private def representation (catalog : Catalog) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.representations) (fun state table => {state with representations := table})
    (fun input path => do
      let status := DecoderValues.parseStatus (← catalog.string (← catalog.field input "status" path) path)
      unless status == .supported do return {
        status, transparent := false, c := false, rust := false, simd := false, packBytes := none }
      let flag := fun key => do catalog.boolean (← catalog.field input key path) path
      let optionalNat := fun key => do
        match ← nullable catalog input key path with
        | none => pure none
        | some value => some <$> value.getNat?
      let integer ← match ← nullable catalog input "integer" path with
        | none => pure none
        | some value =>
          let signed ← catalog.boolean (← catalog.field value "signed" path) path
          let value ← match ← catalog.string (← catalog.field value "kind" path) path with
            | "pointer_sized" => pure (RepresentationInteger.pointer signed)
            | "fixed" => pure (RepresentationInteger.fixed
                (DecoderValues.integerTypeTag (← catalog.string (← catalog.field value "integer_kind" path) path))
                (← catalog.natural (← catalog.field value "size_bits" path) path) signed)
            | _ => throw s!"{path}: unknown representation integer"
          pure (some value)
      let scalableElement ← match ← nullable catalog input "scalable_element" path with
        | none => pure none
        | some value =>
          let value ← match ← catalog.string (← catalog.field value "kind" path) path with
            | "container" => pure ScalableRepresentation.container
            | "element_count" => pure (ScalableRepresentation.elementCount
                (← catalog.natural (← catalog.field value "count" path) path))
            | _ => throw s!"{path}: unknown scalable representation"
          pure (some value)
      return {
        status := status
        transparent := (← flag "transparent")
        c := (← flag "c")
        rust := (← flag "rust")
        simd := (← flag "simd")
        packBytes := (← optionalNat "pack_bytes")
        integer := integer
        alignBytes := (← optionalNat "align_bytes")
        flagsBits := (← catalog.natural (← catalog.field input "flags_bits" path) path)
        scalableElement := scalableElement }) input path

private def arrayConstructor (catalog : Catalog) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.arrayConstructors) (fun state table => {state with arrayConstructors := table})
    (fun input path => do
      let status := DecoderValues.parseStatus (← catalog.string (← catalog.field input "status" path) path)
      unless status == .supported do return ⟨status,false,0⟩
      return ⟨status,← catalog.boolean (← catalog.field input "canonical_value_constructor" path) path,
        ← catalog.natural (← catalog.field input "count" path) path⟩) input path

private def relations (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode TypeRelations := do
  let shape ← catalog.field input "shape" path
  let status ← catalog.string (← catalog.field shape "status" path) path
  if status != "supported" then return {}
  let kind ← catalog.string (← catalog.field shape "kind" path) path
  match kind with
  | "tuple" => return {elements := some (← typeList catalog count (← catalog.field shape "elements" path) path)}
  | "array" | "slice" =>
    let constructor ← match ← catalog.optionalField shape "constructor_identity" path with
      | none | some .null => pure none
      | some value => some <$> arrayConstructor catalog value path
    return {element := some (← typeId catalog count (← catalog.field shape "element" path) path), arrayConstructor := constructor}
  | "reference" | "raw_pointer" =>
    let mutability ← catalog.field shape "mutability" path
    let mutable ← match ← catalog.string (← catalog.field mutability "kind" path) path with
      | "mutable" => pure true | "immutable" => pure false | _ => throw s!"{path}: unknown pointer mutability"
    return {pointee := some (← typeId catalog count (← catalog.field shape "pointee" path) path), mutable := some mutable}
  | "closure" => return {upvarCount := some (← catalog.natural (← catalog.field shape "upvar_count" path) path)}
  | "pattern_type" => return {base := some (← typeId catalog count (← catalog.field shape "base" path) path)}
  | "unsafe_binder" => return {inner := some (← typeId catalog count (← catalog.field shape "inner" path) path)}
  | "adt" => return {
    variants := some (← variants catalog count (← catalog.field shape "variants" path) path)
    representation := some (← representation catalog (← catalog.field shape "representation" path) path)}
  | _ => return {}

end Miri.Input.Reader.TypeRelationsReader

namespace Miri.Input.Reader
open Lean Miri.MIR

def Catalog.readTypeRelations (catalog : Catalog) : Except String (Array TypeRelations × TypeRelationTables) := do
  let values ← catalog.array (← catalog.field catalog.root "types" "$") "$.types"
  let initial : TypeRelationTables := {
    representations := Array.replicate catalog.nodes.size none
    arrayConstructors := Array.replicate catalog.nodes.size none
    typeLists := Array.replicate catalog.nodes.size none
    fields := Array.replicate catalog.nodes.size none
    fieldLists := Array.replicate catalog.nodes.size none
    variants := Array.replicate catalog.nodes.size none
    variantLists := Array.replicate catalog.nodes.size none }
  (values.mapIdxM fun index value =>
    TypeRelationsReader.relations catalog values.size value s!"$.types[{index}]").run initial

end Miri.Input.Reader
