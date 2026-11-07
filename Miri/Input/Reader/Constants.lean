import Miri.Input.Reader.Generics
import Miri.Input.Reader.SourceSpan

namespace Miri.Input.Reader.ConstantReader
open Lean Miri.MIR

structure Context where
  typeCount : Nat
  allocationCount : Nat
  scalarSizes : Array (Option Nat)

abbrev State := MIRReader.State
abbrev Decode := MIRReader.Decode

def span (catalog : Catalog) (input : Json) (path : String) : Decode SpanRef := do
  let slot ← catalog.readCached (·.spanIds) (fun state spanIds => {state with spanIds})
    (fun input path => do
      let value ← catalog.decodeSourceSpan input path
      let state ← get
      let compiler := state.compiler
      if let some index := compiler.spans.idxOf? value then return ⟨index⟩
      let index := compiler.spans.size
      set {state with compiler := {compiler with spans := compiler.spans.push value}}
      return ⟨index⟩) input path
  let state ← get
  state.spanIds.lookup slot |>.mapError (fun id => s!"{path}: missing span {id}")

private def typeId (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String TyId := do
  let id ← catalog.natural (← catalog.field input "type_id" path) path
  unless id < count do throw s!"{path}: invalid type ID {id}"
  return id

private def allocationId (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String AllocationId := do
  let id ← catalog.natural (← catalog.field input "allocation_id" path) path
  unless id < count do throw s!"{path}: invalid allocation ID {id}"
  return id

private def number (catalog : Catalog) (input : Json) (path : String) : Except String Nat := do
  let text ← catalog.string input path
  let some value := text.toNat? | throw s!"{path}: invalid decimal integer"
  return value

def evaluated (catalog : Catalog) (ctx : Context) (ty : TyId) (input : Json) (path : String) : Except String ConstValue := do
  let field := fun key => catalog.field input key path
  let natural := fun key => do catalog.natural (← field key) path
  match ← catalog.string (← field "kind") path with
  | "zero_sized" => return .ZeroSized
  | "scalar" =>
    let bits ← number catalog (← field "bits_unsigned") path
    let some (some size) := ctx.scalarSizes[ty]? | throw s!"{path}: missing scalar width for type {ty}"
    unless size > 0 && bits < 2 ^ (8 * size) do throw s!"{path}: scalar bits exceed byte width"
    return .Scalar (.Int bits size)
  | "pointer_scalar" =>
    return .Scalar (.Ptr (.Allocation (← allocationId catalog ctx.allocationCount (← field "allocation") path)
      (← natural "offset_bytes") (← catalog.boolean (← field "immutable") path)
      (← catalog.boolean (← field "shared_ref") path)))
  | "pointer_scalar_without_provenance" =>
    return .Scalar (.Ptr (.Address (← number catalog (← field "address") path) (← natural "address_width_bytes")))
  | "slice_allocation" => return .Slice (← allocationId catalog ctx.allocationCount (← field "allocation") path) (← natural "metadata_length")
  | "indirect_allocation" => return .Indirect (← allocationId catalog ctx.allocationCount (← field "allocation") path) (← natural "offset_bytes")
  | kind => throw s!"{path}: unsupported evaluated constant {kind}"

private def optionalNatural (catalog : Catalog) (input : Json) (path : String) : Except String (Option Nat) := do
  let input ← catalog.inspect input path
  if input == .null then return none
  return some (← catalog.natural input path)

private def value (catalog : Catalog) (ctx : Context) (input : Json) (path : String) : Decode ConstantNode := do
  catalog.requireSupported input path
  let field := fun key => catalog.field input key path
  let ty ← typeId catalog ctx.typeCount (← field "type") path
  let annotation ← catalog.inspect (← field "user_type_annotation") path
  let userType ← if annotation == .null then pure none else
    match annotation.getNat? with
    | .ok id => pure (some id)
    | .error _ => some <$> catalog.natural (← catalog.field annotation "index" path) path
  let span ← span catalog (← field "span") path
  let constant ← field "constant"
  let evaluation : Except String ConstValue := do
    catalog.requireSupported constant path
    evaluated catalog ctx ty (← catalog.field constant "value" path) path
  let source ← catalog.field constant "source" path
  let sourceField := fun key => catalog.field source key path
  let mirConstant ← (show Decode MirConst from do
    match ← catalog.string (← sourceField "kind") path with
    | "already_evaluated" => return .Val (← evaluation) ty
    | "type_system_const" =>
      let sourceType ← typeId catalog ctx.typeCount (← sourceField "type") path
      let id ← GenericReader.constant catalog ctx.typeCount (← sourceField "const") path
      let state ← get
      let some value := state.compiler.typeConstants[id]? | throw s!"{path}: missing type constant {id}"
      return .Ty sourceType value
    | "unevaluated" =>
      let definition ← GenericReader.definition catalog (← sourceField "def_id") path
      let id ← GenericReader.arguments catalog ctx.typeCount (← sourceField "generic_args") path
      let state ← get
      let arguments ← state.arguments.lookup id |>.mapError (fun id => s!"{path}: missing arguments {id}")
      return .Unevaluated ⟨definition, arguments, ← optionalNatural catalog (← sourceField "promoted") path⟩
        (← typeId catalog ctx.typeCount (← sourceField "type") path)
    | kind => throw s!"{path}: unsupported MIR constant source {kind}")
  return ⟨⟨span, userType, mirConstant⟩,evaluation⟩

def constant (catalog : Catalog) (ctx : Context) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.tables.constants) (fun state constants => {state with tables := {state.tables with constants}})
    (value catalog ctx) input path

end Miri.Input.Reader.ConstantReader
