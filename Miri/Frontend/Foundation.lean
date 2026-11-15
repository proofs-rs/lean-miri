import Lean
import Miri.Frontend.FoundationExistential
import Miri.Frontend.FoundationSource

/-! Finite, structural rustc material for pure, demand-time Lean queries.  This
format has no compiler answer table.  It is distinct from executable MIR input:
only the cases implemented below can be resolved, and missing cases fail. -/

namespace Miri.Frontend.Foundation
open Lean

structure Target where
  triple : String
  architecture : String := ""
  dataLayout : String
  pointerSizeBits : Nat
  endian : String
  runtimeDataLayout : Json := Json.null

structure Document where
  source : Json
  target : Target
  definitions : Array Json
  types : Array Json
  bodies : Array Json

private def field (j : Json) (key : String) : Except String Json :=
  (j.getObjVal? key).mapError fun e => s!"{key}: {e}"

private def string (j : Json) (key : String) : Except String String :=
  (j.getObjValAs? String key).mapError fun e => s!"{key}: {e}"

private def nat (j : Json) (key : String) : Except String Nat :=
  (j.getObjValAs? Nat key).mapError fun e => s!"{key}: {e}"

private def array (j : Json) (key : String) : Except String (Array Json) :=
  (j.getObjValAs? (Array Json) key).mapError fun e => s!"{key}: {e}"

def decode (j : Json) : Except String Document := do
  unless (← string j "schema") == "lean-miri-foundation" do
    throw "unexpected foundation schema"
  unless (← nat j "schema_version") == 1 do
    throw "unsupported foundation schema version"
  unless (← string j "rustc_commit") == "8144389c895da997dbdecaa635e41d6a50be6ffd" do
    throw "foundation material uses a different rustc revision"
  let t ← field j "target"
  let target : Target := {
    triple := ← string t "triple"
    architecture := ← string t "architecture"
    dataLayout := ← string t "data_layout"
    pointerSizeBits := ← nat t "pointer_size_bits"
    endian := ← string t "endian"
    runtimeDataLayout := ← field t "runtime_data_layout"
  }
  unless target.pointerSizeBits > 0 && target.pointerSizeBits % 8 == 0 do
    throw "invalid target pointer width"
  unless target.endian == "little" || target.endian == "big" do
    throw "invalid target endianness"
  let definitions ← array j "definitions"
  let types ← array j "types"
  let bodies ← array j "bodies"
  for h : i in [:types.size] do
    unless (← nat types[i] "type_id") == i do
      throw s!"types[{i}]: type IDs must be dense"
    let _ ← field types[i] "shape"
  for h : i in [:definitions.size] do
    unless (← nat definitions[i] "definition_id") == i do
      throw s!"definitions[{i}]: definition IDs must be dense"
  for body in bodies do
    unless (← nat body "definition") < definitions.size do
      throw "body definition is out of bounds"
    let _ ← array body "required_consts"
    validateSourceMetadata body
    for localType in (← array body "locals") do
      unless (← localType.getNat?) < types.size do
        throw "body local type is out of bounds"
  return ⟨j, target, definitions, types, bodies⟩

inductive ConstExpr where
  | parameter (index : Nat)
  | value (value : Nat)
  deriving Repr, DecidableEq

inductive TypeExpr where
  | primitive (kind name : String)
  | closure (definition : Nat) (arguments : Array TypeExpr)
  | nominal (definition : Nat) (arguments : Array TypeExpr)
  | parameter (index : Nat)
  | array (element : TypeExpr) (length : ConstExpr)
  | tuple (elements : Array TypeExpr)
  | pointer (kind : String) (pointee : TypeExpr)
  | patternNotNull (base : TypeExpr)
  | dynamicObject (source : ExistentialType TypeExpr)
  | functionPointer (inputs : Array TypeExpr) (output : TypeExpr) (safety abi : String) (cVariadic : Bool)
  deriving Repr

private def constant (j : Json) : Except String ConstExpr := do
  match ← string j "kind" with
  | "param" => return .parameter (← nat j "index")
  | "value" =>
    let bits ← string j "bits"
    let some value := bits.toNat? | throw "invalid scalar constant"
    return .value value
  | other => throw s!"unsupported foundation constant {other}"

/-- Resolve a source type only when requested.  The fuel bounds recursive type
references, including malformed cycles; no compiler query result is read. -/
def typeExpr (d : Document) (id : Nat) : Except String TypeExpr :=
  go d.types.size #[] id
where
  go (fuel : Nat) (seen : Array Nat) (id : Nat) : Except String TypeExpr := do
    if seen.contains id then throw "cyclic foundation type reference"
    let some row := d.types[id]? | throw s!"missing foundation type {id}"
    let shape ← field row "shape"
    let kind ← string shape "kind"
    let .succ remaining := fuel | throw "foundation type resolution exhausted"
    let seen := seen.push id
    match kind with
    | "closure" =>
      let definition ← nat shape "definition"
      let parentCount ← nat shape "parent_count"
      let sourceArgs ← array shape "arguments"
      unless sourceArgs.size == parentCount + 3 do throw "closure synthetic argument count mismatch"
      let mut args := #[]
      for arg in sourceArgs do
        unless (← string arg "kind") == "type" do throw "closure non-type argument unsupported"
        args := args.push (← go remaining seen (← nat arg "type"))
      for (name, ordinal) in #[("kind_type", 0), ("signature_type", 1), ("tupled_upvars_type", 2)] do
        let some arg := sourceArgs[parentCount + ordinal]? | throw "closure synthetic argument absent"
        unless (← nat arg "type") == (← nat shape name) do throw "closure synthetic argument identity mismatch"
      return .closure definition args
    | "adt" =>
      let mut args := #[]
      for arg in ← array shape "arguments" do
        unless (← string arg "kind") == "type" do throw "unsupported nominal generic argument"
        args := args.push (← go remaining seen (← nat arg "type"))
      return .nominal (← nat shape "definition") args
    | "param" => return .parameter (← nat shape "index")
    | "array" =>
      let element ← go remaining seen (← nat shape "element")
      let length ← constant (← field shape "length")
      return .array element length
    | "tuple" =>
      let mut elements := #[]
      for entry in (← array shape "elements") do
        elements := elements.push (← go remaining seen (← entry.getNat?))
      return .tuple elements
    | "pattern_type" =>
      let pattern ← field shape "pattern"
      unless (← string pattern "kind") == "not_null" do throw "unsupported source type pattern"
      return .patternNotNull (← go remaining seen (← nat shape "base"))
    | "raw_pointer" =>
      let mutable ← shape.getObjValAs? Bool "mutable"
      let tag := if mutable then "raw_pointer_mut" else "raw_pointer_const"
      return .pointer tag (← go remaining seen (← nat shape "pointee"))
    | "reference" =>
      let mutable ← shape.getObjValAs? Bool "mutable"
      let region ← string shape "region"
      unless region == "static" || region == "erased" do
        throw "unsupported reference region"
      let tag := s!"reference_{region}_{if mutable then "mut" else "const"}"
      return .pointer tag (← go remaining seen (← nat shape "pointee"))
    | "dynamic" => return .dynamicObject (← parseExistential d.definitions (go remaining seen) shape)
    | "function_pointer" =>
      let signature ← field shape "signature"
      unless (← array signature "bound_variables").isEmpty do
        throw "bound function-pointer signature unsupported"
      let safety ← string signature "safety"
      unless safety == "safe" || safety == "unsafe" do throw "invalid function-pointer safety"
      let abi ← field signature "abi"
      let abiKind ← string abi "kind"
      unless (abiKind == "rust" || abiKind == "rust_call") && (← field abi "unwind") == Json.null do
        throw "function-pointer ABI unsupported"
      let variadic ← signature.getObjValAs? Bool "c_variadic"
      unless !variadic do throw "variadic function pointer unsupported"
      let mut inputs := #[]
      for input in (← array signature "inputs") do
        inputs := inputs.push (← go remaining seen (← input.getNat?))
      return .functionPointer inputs (← go remaining seen (← nat signature "output")) safety abiKind variadic
    | "bool" | "char" | "never" | "str" => return .primitive kind ""
    | "int" | "uint" | "float" => return .primitive kind (← string shape "name")
    | other => throw s!"unsupported demand-time foundation type {other}"

def ConstExpr.instantiate (constants : Array (Option Nat)) : ConstExpr → Except String Nat
  | .value v => pure v
  | .parameter i =>
    match constants[i]?.bind id with
    | some v => pure v
    | none => throw s!"missing const argument {i}"

inductive ConcreteType where
  | primitive (kind name : String)
  | closure (definition : Nat) (arguments : Array ConcreteType)
  | nominal (definition : Nat) (arguments : Array ConcreteType)
  | array (element : ConcreteType) (length : Nat)
  | tuple (elements : Array ConcreteType)
  | pointer (kind : String) (pointee : ConcreteType)
  | patternNotNull (base : ConcreteType)
  | dynamicObject (source : ExistentialType ConcreteType)
  | functionPointer (inputs : Array ConcreteType) (output : ConcreteType) (safety abi : String) (cVariadic : Bool)
  deriving Repr

/-- Substitute a demand's generic arguments in Lean.  Both arrays use rustc's
unified parameter indices; absent entries preserve the type/const distinction. -/
def instantiate (types : Array (Option ConcreteType)) (constants : Array (Option Nat))
    (expr : TypeExpr) : Except String ConcreteType := go 1024 expr
where
  go (fuel : Nat) (expr : TypeExpr) : Except String ConcreteType := do
    let .succ remaining := fuel | throw "foundation instantiation exhausted"
    match expr with
    | .primitive kind name => return .primitive kind name
    | .closure definition arguments => return .closure definition (← arguments.mapM (go remaining))
    | .nominal definition arguments => return .nominal definition (← arguments.mapM (go remaining))
    | .parameter i =>
      match types[i]?.bind id with
      | some ty => return ty
      | none => throw s!"missing type argument {i}"
    | .array element length =>
      return .array (← go remaining element) (← length.instantiate constants)
    | .tuple elements =>
      return .tuple (← elements.mapM (go remaining))
    | .pointer kind pointee => return .pointer kind (← go remaining pointee)
    | .patternNotNull base => return .patternNotNull (← go remaining base)
    | .dynamicObject source => return .dynamicObject (← mapExistentialM (go remaining) source)
    | .functionPointer inputs output safety abi variadic =>
      return .functionPointer (← inputs.mapM (go remaining)) (← go remaining output) safety abi variadic

end Miri.Frontend.Foundation
