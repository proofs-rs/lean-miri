import Miri.Input.Reader.Regions
import Miri.Input.DecoderValues

namespace Miri.Input.Reader.GenericReader
open Lean Miri.MIR

abbrev State := MIRReader.State
abbrev Decode := MIRReader.Decode

def definition (catalog : Catalog) (input : Json) (path : String) : Decode DefId :=
  RegionReader.definition catalog input path

private def typeId (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String TyId := do
  let id ← catalog.natural (← catalog.field input "type_id" path) path
  unless id < count do throw s!"{path}: invalid type ID {id}"
  return id

private def intern (constant : TypeConst) : Decode TypeConstId := do
  let state ← get
  let table := state.compiler.typeConstants
  if let some index := table.idxOf? constant then return index
  set {state with compiler := {state.compiler with typeConstants := table.push constant}}
  return table.size

mutual
partial def arguments (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode Nat :=
  catalog.readCached (·.arguments) (fun state arguments => {state with arguments})
    (fun input path => do
      (← catalog.array input path).mapIdxM fun index arg => do
        let path := s!"{path}[{index}]"
        let value ← catalog.field arg "value" path
        match ← catalog.string (← catalog.field arg "kind" path) path with
        | "type" => return .Type (← typeId catalog count value path)
        | "lifetime" =>
          let id ← RegionReader.region catalog value path
          let state ← get
          return .Lifetime (← state.regions.lookup id |>.mapError (fun id => s!"{path}: missing region {id}"))
        | "const" => return .Const (← constant catalog count value path)
        | kind => throw s!"{path}: unsupported generic argument {kind}") input path

partial def constant (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode TypeConstId := do
  let id ← catalog.readCached (·.typeConstantIds) (fun state typeConstantIds => {state with typeConstantIds})
    (fun input path => do intern (← constantValue catalog count input path)) input path
  let state ← get
  state.typeConstantIds.lookup id |>.mapError (fun id => s!"{path}: missing type constant {id}")

private partial def argumentValues (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode (Array GenericArg) := do
  let id ← arguments catalog count input path
  let state ← get
  state.arguments.lookup id |>.mapError (fun id => s!"{path}: missing generic arguments {id}")

private partial def constantValue (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode TypeConst := do
  let field := fun key => catalog.field input key path
  let natural := fun key => do catalog.natural (← field key) path
  let text := fun key => do catalog.string (← field key) path
  let kind ← text "kind"
  -- A template parameter is an exact symbolic term, not a concrete value.
  -- rustc cannot give ConstKind::Param a declared type; the exporter therefore
  -- marks it incomplete. Preserve the term and its source obligation instead
  -- of rejecting the entire import or inventing an evaluated count.
  let status ← text "status"
  unless status == "supported" || (kind == "parameter" && status == "incomplete") do
    throw s!"{path}: compiler payload is unavailable"
  match kind with
  | "parameter" =>
    let declared ← catalog.inspect (← field "declared_type") path
    let declared ← if declared == .null then pure none else
      match declared.getObjVal? "status" with
      | .ok status =>
        unless (← catalog.string status path) == "unknown" do throw s!"{path}: invalid declared type metadata"
        pure none
      | .error _ => some <$> typeId catalog count declared path
    return .Param (← natural "index") (← text "name") declared
  | "inference" =>
    let inference ← field "inference"
    let index ← catalog.natural (← catalog.field inference "index" path) path
    match ← catalog.string (← catalog.field inference "kind" path) path with
    | "variable" => return .InferVar index
    | "fresh" => return .InferFresh index
    | kind => throw s!"{path}: unsupported const inference {kind}"
  | "bound" => return .Bound (← RegionReader.boundIndex catalog (← field "index_kind") path) (← natural "variable_index")
  | "placeholder" => return .Placeholder (← natural "universe") (← natural "variable_index")
  | "alias" =>
    let kind ← (show Decode ConstAliasKind from do
      match ← text "alias_kind" with
      | "projection" => return .Projection
      | "inherent_self" => return .InherentSelf
      | "inherent_impl" => return .InherentImpl
      | "free" => return .Free
      | "anonymous" => return .Anon
      | kind => throw s!"{path}: unsupported const alias {kind}")
    let rigid ← match ← text "rigidity" with
      | "rigid" => pure true
      | "not_rigid" => pure false
      | kind => throw s!"{path}: unsupported const rigidity {kind}"
    return .Alias rigid kind (← definition catalog (← field "def_id") path)
      (← argumentValues catalog count (← field "generic_args") path)
  | "value" =>
    return .Value (← typeId catalog count (← field "type") path)
      (← valTree catalog count (← field "value") path)
  | "error" => return .Error
  | "expression" =>
    let kind ← (show Decode ConstExpressionKind from do
      match ← text "expression_kind" with
      | "binary_operator" =>
        let operator ← catalog.field (← field "operator") "kind" path
        let some op := DecoderValues.binOpFromExportTag (← catalog.string operator path)
          | throw s!"{path}: unsupported abstract binary operator"
        return .Binop op
      | "unary_operator" =>
        let operator ← catalog.field (← field "operator") "kind" path
        let some op := DecoderValues.unOpFromExportTag (← catalog.string operator path)
          | throw s!"{path}: unsupported abstract unary operator"
        return .UnOp op
      | "function_call" => return .FunctionCall
      | "cast" =>
        match ← text "operator" with
        | "as" => return .Cast .As
        | "use" => return .Cast .Use
        | kind => throw s!"{path}: unsupported abstract const cast {kind}"
      | kind => throw s!"{path}: unsupported const expression {kind}")
    return .Expr kind (← argumentValues catalog count (← field "arguments") path)
  | kind => throw s!"{path}: unsupported type constant {kind}"

private partial def valTree (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Decode ValTree := do
  match ← catalog.string (← catalog.field input "kind" path) path with
  | "leaf" =>
    let size ← catalog.natural (← catalog.field input "size_bytes" path) path
    let text ← catalog.string (← catalog.field input "bits_unsigned" path) path
    let some bits := text.toNat? | throw s!"{path}: invalid scalar decimal"
    unless size > 0 && bits < 2 ^ (size * 8) do throw s!"{path}: invalid valtree scalar width"
    return ⟨#[.Leaf bits size], 0⟩
  | "branch" =>
    let children ← (← catalog.array (← catalog.field input "elements" path) path).mapIdxM
      fun index child => constant catalog count child s!"{path}[{index}]"
    return ⟨#[.Branch children], 0⟩
  | kind => throw s!"{path}: unsupported valtree {kind}"
end

end Miri.Input.Reader.GenericReader
