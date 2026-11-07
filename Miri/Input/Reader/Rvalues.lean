import Miri.Input.Reader.Operands
import Miri.Input.Reader.Operations
import Miri.Input.Reader.ThreadLocalQueries

namespace Miri.Input.Reader.RvalueReader
open Lean Miri.MIR

abbrev State := MIRReader.State
abbrev Decode := MIRReader.Decode

private def typeId (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String TyId := do
  let id ← catalog.natural (← catalog.field input "type_id" path) path
  unless id < count do throw s!"{path}: invalid type ID {id}"
  return id

private def optionalIndex (catalog : Catalog) (input : Json) (path : String) (annotation : Bool := false) : Except String (Option Nat) := do
  let input ← catalog.inspect input path
  if input == .null then return none
  if annotation then
    match input.getNat? with
    | .ok index => return some index
    | .error _ => return some (← catalog.natural (← catalog.field input "index" path) path)
  return some (← catalog.natural input path)

private def aggregate (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode AggregateNode := do
  let field := fun key => catalog.field input key path
  let definition := do (GenericReader.definition catalog (← field "def_id") path)
  let arguments := do (GenericReader.arguments catalog count (← field "generic_args") path)
  match ← catalog.string (← field "kind") path with
  | "Array" => return .Array (← typeId catalog count (← field "element_type") path)
  | "Tuple" => return .Tuple
  | "Adt" =>
    return .Adt (← definition) (← catalog.natural (← field "variant_index") path) (← arguments)
      (← optionalIndex catalog (← field "user_type_annotation") path true)
      (← optionalIndex catalog (← field "active_union_field") path)
  | "Closure" => return .Closure (← definition) (← arguments)
  | "Coroutine" => return .Coroutine (← definition) (← arguments)
  | "CoroutineClosure" => return .CoroutineClosure (← definition) (← arguments)
  | "RawPtr" =>
    return .RawPtr (← typeId catalog count (← field "pointee_type") path)
      (← catalog.mutability (← field "mutability") path)
  | kind => throw s!"{path}: unsupported aggregate kind {kind}"

private def value (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode RvalueNode := do
  let field := fun key => catalog.field input key path
  let operand := fun key => do (OperandReader.operand catalog ctx (← field key) path)
  let place := do (OperandReader.place catalog ctx.typeCount (← field "place") path)
  let ty := fun key => do typeId catalog ctx.typeCount (← field key) path
  unless (← catalog.string (← field "status") path) == "supported" do throw s!"{path}: unsupported rvalue"
  match ← catalog.string (← field "kind") path with
  | "Use" =>
    let retag ← match ← catalog.string (← catalog.field (← field "retag") "kind" path) path with
      | "yes" => pure WithRetag.Yes
      | "no" => pure .No
      | kind => throw s!"{path}: unsupported retag mode {kind}"
    return .Use (← operand "operand") retag
  | "BinaryOp" =>
    let some op := DecoderValues.binOpFromExportTag (← catalog.string (← catalog.field (← field "operator") "kind" path) path)
      | throw s!"{path}: unsupported binary operator"
    return .BinaryOp op (← operand "left") (← operand "right")
  | "UnaryOp" =>
    let some op := DecoderValues.unOpFromExportTag (← catalog.string (← catalog.field (← field "operator") "kind" path) path)
      | throw s!"{path}: unsupported unary operator"
    return .UnaryOp op (← operand "operand")
  | "Discriminant" => return .Discriminant (← place)
  | "CopyForDeref" => return .CopyForDeref (← place)
  | "WrapUnsafeBinder" => return .WrapUnsafeBinder (← operand "operand") (← ty "type")
  | "Repeat" =>
    return .Repeat (← operand "operand")
      (← (GenericReader.constant catalog ctx.typeCount (← field "count") path))
  | "Ref" =>
    return .Ref (← (RegionReader.region catalog (← field "region") path))
      (← catalog.borrowKind (← field "borrow_kind") path) (← place)
  | "ThreadLocalRef" =>
    let definition ← GenericReader.definition catalog (← field "def_id") path
    ThreadLocalQueryReader.register catalog definition input path
    return .ThreadLocalRef definition
  | "RawPtr" =>
    let kind ← match ← catalog.string (← catalog.field (← field "pointer_kind") "kind" path) path with
      | "mutable" => pure RawPtrKind.Mut
      | "constant" => pure .Const
      | "metadata_only" => pure .FakeForPtrMetadata
      | kind => throw s!"{path}: unsupported raw pointer kind {kind}"
    return .RawPtr kind (← place)
  | "Cast" => return .Cast (← catalog.castKind (← field "cast_kind") path) (← operand "operand") (← ty "target_type")
  | "Aggregate" =>
    return .Aggregate (← aggregate catalog ctx.typeCount (← field "aggregate_kind") path)
      (← (OperandReader.operands catalog ctx (← field "operands") path))
  | "Reborrow" => return .Reborrow (← ty "type") (← catalog.mutability (← field "mutability") path) (← place)
  | kind => throw s!"{path}: unsupported rvalue kind {kind}"

def rvalue (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode RvalueId := do
  return ⟨← catalog.readCached (·.tables.rvalues) (fun state rvalues => {state with tables := {state.tables with rvalues}})
    (value catalog ctx) input path⟩


end Miri.Input.Reader.RvalueReader
