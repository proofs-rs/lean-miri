import Miri.Frontend.FoundationSourceTypes
import Miri.Input.Model.SourceConstValues

/-! The producer's scalar/ZST CTFE values are trusted compiler observations.
Groundness and value representation are checked once at this ingestion boundary. -/
namespace Miri.Frontend.Foundation.SourceConstValuesParser
open Lean Miri Input.SourceTypes
private def closedRegion : Region → Bool
  | .static | .erased => true
  | _ => false
private def scalarBytes (pointerBits : Nat) : Input.SourceTypes.Expr → Option Nat
  | .primitive "bool" _ => some 1
  | .primitive "char" _ => some 4
  | .primitive "int" name | .primitive "uint" name =>
    if name == "isize" || name == "usize" then some (pointerBits / 8)
    else if name == "i8" || name == "u8" then some 1
    else if name == "i16" || name == "u16" then some 2
    else if name == "i32" || name == "u32" then some 4
    else if name == "i64" || name == "u64" then some 8
    else if name == "i128" || name == "u128" then some 16 else none
  | .primitive "float" name => if name == "f32" then some 4 else if name == "f64" then some 8 else none
  | _ => none

private def scalarValid (pointerBits : Nat) (type : Input.SourceTypes.Expr) (bits bytes : Nat) : Bool :=
  bytes > 0 && bytes ≤ 16 && bits < 2^(8*bytes) && scalarBytes pointerBits type == some bytes &&
    match type with
    | .primitive "bool" _ => bits ≤ 1
    | .primitive "char" _ => bits ≤ 0x10ffff && !(0xd800 ≤ bits && bits ≤ 0xdfff)
    | _ => true

private def groundConst (source : Material) (pointerBits : Nat) : ConstExpr → Bool
  | .value ref bits bytes => source.types[ref]?.any (fun type => scalarValid pointerBits type bits bytes)
  | _ => false

mutual
private def groundType (source : Material) (pointerBits fuel : Nat) (ref : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel + 1 => match source.types[ref]? with
    | some (.primitive ..) => true
    | some (.tuple refs) => refs.all (groundType source pointerBits fuel)
    | some (.array element length) => groundType source pointerBits fuel element && groundConst source pointerBits length
    | some (.rawPointer child _) | some (.patternNotNull child) => groundType source pointerBits fuel child
    | some (.reference child _ region) => closedRegion region && groundType source pointerBits fuel child
    | some (.nominal _ args) | some (.functionDefinition _ args) => args.all (groundArg source pointerBits fuel)
    | some (.closure closure) => closure.arguments.all (groundArg source pointerBits fuel)
    | some (.functionPointer signature) => signature.boundVariables.isEmpty &&
        signature.inputs.all (groundType source pointerBits fuel) && groundType source pointerBits fuel signature.output
    | some (.dynamicObject region predicates) => closedRegion region && predicates.all (fun predicate =>
        match predicate with
        | .trait _ args bounds => bounds.isEmpty && args.all (groundArg source pointerBits fuel)
        | .projection _ _ args term bounds => bounds.isEmpty && args.all (groundArg source pointerBits fuel) && groundType source pointerBits fuel term
        | .autoTrait _ bounds => bounds.isEmpty
        | .unsupported _ => false)
    | _ => false
private def groundArg (source : Material) (pointerBits fuel : Nat) : Argument → Bool
  | .type ref => groundType source pointerBits fuel ref
  | .lifetime region => closedRegion region
  | .constant value => groundConst source pointerBits value

end

def material (json : Json) (source : Material) (pointerBits : Nat) : Except String (Option Input.SourceConstValues.Material) := do
  let some encoded := (json.getObjVal? "evaluated_const_values").toOption | return none
  if encoded == .null then return none
  let mut rows : Array Input.SourceConstValues.Row := #[]
  for encodedRow in (← encoded.getObjValAs? (Array Json) "rows") do
    let definitionRef ← encodedRow.getObjValAs? Nat "definition"
    let some definition := source.definitions[definitionRef]? | throw "concrete const definition reference absent"
    let arguments ← (← encodedRow.getObjValAs? (Array Json) "arguments").mapM SourceTypesParser.argument
    let parameters ← encodedRow.getObjValAs? (Array String) "parameters"
    unless arguments.size == parameters.size do throw "concrete const key argument count mismatch"
    for argument in arguments, parameter in parameters do
      unless (match argument with | .type _ => "type" | .lifetime _ => "lifetime" | .constant _ => "const") == parameter do
        throw "concrete const key parameter kind mismatch"
    unless arguments.all (groundArg source pointerBits (source.types.size + 1)) do throw "concrete const key is not ground"
    let promoted ← encodedRow.getObjValAs? (Option Nat) "promoted"
    let typeRef ← encodedRow.getObjValAs? Nat "type"
    let some resultType := source.types[typeRef]? | throw "concrete const result type absent"
    let encodedValue ← encodedRow.getObjVal? "value"
    let value ← match ← encodedValue.getObjValAs? String "kind" with
      | "scalar" => do
        let text ← encodedValue.getObjValAs? String "bits"
        let some bits := text.toNat? | throw "invalid concrete const scalar bits"
        let bytes ← encodedValue.getObjValAs? Nat "size_bytes"
        unless scalarValid pointerBits resultType bits bytes do
          throw "concrete const scalar value/type/width mismatch"
        pure (Input.SourceConstValues.Value.scalar bits bytes)
      | "zero_sized" => do
        unless resultType == .tuple #[] do throw "unproved concrete const zero-sized type"
        pure .zeroSized
      | _ => throw "unsupported concrete const value kind"
    if rows.any (fun row => row.definition == definition.raw && row.arguments == arguments && row.promoted == promoted) then
      throw "duplicate concrete const key"
    rows := rows.push ⟨definition.raw, arguments, promoted, typeRef, value⟩
  return some ⟨rows⟩
/-- Join only exact original ground keys. Syntactically different normalized
keys conservatively miss. No unrelated candidate is instantiated or evaluated. -/
def attachAliasValues (source : Material) (values : Option Input.SourceConstValues.Material) : Except String Material := do
  let some values := values | return source
  let aliases ← source.constantAliases.mapM fun alias => do
    if alias.kind == .InherentSelf then return alias
    let some declaration := source.definitions[alias.definition]? | throw "const alias declaration absent"
    let candidates := values.rows.filter fun row => row.definition == declaration.raw &&
      row.promoted.isNone && row.arguments == alias.arguments
    if candidates.size > 1 then throw "ambiguous compiler const alias value key"
    let some row := candidates[0]? | return alias
    unless row.typeRef == alias.typeRef do throw "compiler const alias result type mismatch"
    match source.types[alias.typeRef]?, row.value with
    | some (.primitive "uint" "usize"), .scalar bits _ => return {alias with usizeValue := some bits}
    | _,_ => return alias
  return {source with constantAliases := aliases}
end Miri.Frontend.Foundation.SourceConstValuesParser
