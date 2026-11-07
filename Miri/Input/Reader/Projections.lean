import Miri.Input.Reader.Layout

namespace Miri.Input.Reader.ProjectionReader
open Lean Miri.MIR

structure State where
  layouts : SharedTable Layout
  projections : ProjectionTables
abbrev Decode := StateT State (Except String)

private def layout (catalog : Catalog) (input : Json) (path : String) : Decode Nat := do
  let state ← get
  let (id, table) ← catalog.readLayout state.layouts input path
  set {state with layouts := table}
  return id

private def natural (catalog : Catalog) (input : Json) (key path : String) : Decode Nat := do
  catalog.natural (← catalog.field input key path) s!"{path}.{key}"

private def field (catalog : Catalog) (typeCount : Nat) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.projections.fields) (fun state table =>
    {state with projections := {state.projections with fields := table}}) (fun input path => do
      let type ← catalog.field input "type" path
      let typeId ← natural catalog type "type_id" s!"{path}.type"
      unless typeId < typeCount do throw s!"{path}: invalid type ID {typeId}"
      return {
        index := ← natural catalog input "index" path
        typeId := typeId
        layoutId := ← layout catalog (← catalog.field input "layout" path) s!"{path}.layout" }) input path

private def fieldList (catalog : Catalog) (typeCount : Nat) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.projections.fieldLists) (fun state table =>
    {state with projections := {state.projections with fieldLists := table}}) (fun input path => do
      let values ← catalog.array input path
      let mut result := #[]
      for (value, index) in values.toList.zipIdx do
        let id ← field catalog typeCount value s!"{path}[{index}]"
        let entry ← (← get).projections.fields.lookup id |>.mapError (fun id => s!"invalid projection field {id}")
        unless entry.index == index do throw s!"{path}: field index does not match its position"
        result := result.push id
      return result) input path

private def parent (catalog : Catalog) (typeCount : Nat) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.projections.parents) (fun state table =>
    {state with projections := {state.projections with parents := table}}) (fun input path => do
      let variant ← catalog.inspect (← catalog.field input "variant" path) s!"{path}.variant"
      let variant ← if variant == .null then pure none else some <$> variant.getNat?
      return {
        variant := variant
        layoutId := ← layout catalog (← catalog.field input "layout" path) s!"{path}.layout"
        fields := ← fieldList catalog typeCount (← catalog.field input "fields" path) s!"{path}.fields" }) input path

private def parentList (catalog : Catalog) (typeCount : Nat) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.projections.parentLists) (fun state table =>
    {state with projections := {state.projections with parentLists := table}}) (fun input path => do
      let values ← catalog.array input path
      let mut result := #[]
      for (value, index) in values.toList.zipIdx do
        let id ← parent catalog typeCount value s!"{path}[{index}]"
        let entry ← (← get).projections.parents.lookup id |>.mapError (fun id => s!"invalid projection parent {id}")
        let expected := if index == 0 then none else some (index - 1)
        unless entry.variant == expected do throw s!"{path}: variant index does not match its position"
        result := result.push id
      return result) input path

private def value (catalog : Catalog) (typeCount : Nat) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.projections.values) (fun state table =>
    {state with projections := {state.projections with values := table}}) (fun input path => do
      let environment ← catalog.string (← catalog.field input "typing_env" path) s!"{path}.typing_env"
      unless environment == "fully_monomorphized" do throw s!"{path}: typing environment mismatch"
      return {
        typingEnvironment := environment
        parents := ← parentList catalog typeCount (← catalog.field input "parents" path) s!"{path}.parents" }) input path

private def query (catalog : Catalog) (typeCount : Nat) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.projections.queries) (fun state table =>
    {state with projections := {state.projections with queries := table}}) (fun input path => do
      let status := DecoderValues.parseStatus (← catalog.string (← catalog.field input "status" path) s!"{path}.status")
      if status != .supported then return ⟨status, none⟩
      let raw ← catalog.field input "value" path
      if (← catalog.inspect raw s!"{path}.value") == .null then return ⟨status, none⟩
      return ⟨status, some (← value catalog typeCount raw s!"{path}.value")⟩) input path

private def parseTypes (catalog : Catalog) (types : Array Json) : Decode (Array (Option Nat)) := do
  let mut result := #[]
  for (type, index) in types.toList.zipIdx do
    let path := s!"$.types[{index}].compiler_facts"
    let id ← match ← catalog.optionalField type "compiler_facts" path with
      | none | some .null => pure none
      | some facts =>
        let owner ← natural catalog type "type_id" s!"$.types[{index}]"
        let subject ← natural catalog (← catalog.field facts "input_type" path) "type_id" path
        unless owner == subject do throw s!"{path}: compiler fact input type mismatch"
        match ← catalog.optionalField facts "projection_queries" path with
        | none | some .null => pure none
        | some raw => some <$> query catalog types.size raw s!"{path}.projection_queries"
    result := result.push id
  return result

end Miri.Input.Reader.ProjectionReader

namespace Miri.Input.Reader
open Lean Miri.MIR

def Catalog.readProjectionQueries (catalog : Catalog) (layouts : SharedTable Layout) :
    Except String (Array (Option Nat) × SharedTable Layout × ProjectionTables) := do
  let types ← catalog.array (← catalog.field catalog.root "types" "$") "$.types"
  let empty := fun {α : Type} => (Array.replicate catalog.nodes.size none : SharedTable α)
  let initial : ProjectionReader.State := {layouts, projections := {
    fields := empty, fieldLists := empty, parents := empty,
    parentLists := empty, values := empty, queries := empty }}
  let (queries, state) ← (ProjectionReader.parseTypes catalog types).run initial
  return (queries, state.layouts, state.projections)

end Miri.Input.Reader
