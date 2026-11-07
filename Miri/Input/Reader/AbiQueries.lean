import Miri.Input.Reader.Abi
import Miri.Input.Reader.Functions

namespace Miri.Input.Reader
open Lean Miri.MIR

def Catalog.abiReference (catalog : Catalog) (tables : AbiTables) (input : Json) (path : String) : Except String Nat := do
  let some id ← catalog.sharedId? input path | throw s!"{path}: expected shared ABI reference"
  let _ ← tables.functions.lookup id |>.mapError (fun id => s!"{path}: invalid function ABI ID {id}")
  return id

namespace AbiQueryReader
abbrev Decode := MIRReader.Decode

private def path (catalog : Catalog) (input : Json) (keys : List String) : Except String Json :=
  keys.foldlM (fun value key => catalog.field value key key) input

private def reference (catalog : Catalog) (tables : AbiTables) (input : Json)
    (keys : List String) : Except String Nat := do
  let mut query := input
  for key in keys do
    query ← catalog.field query key key
    if key != "recipe" then catalog.requireSupported query key
  catalog.abiReference tables (← catalog.field query "value" "ABI query") "ABI query value"

private def environment (catalog : Catalog) (input : Json) : Except String Unit := do
  unless (← catalog.string (← catalog.field input "typing_env" "ABI query") "ABI query") == "fully_monomorphized" do
    throw "ABI query typing environment mismatch"

private def ty (catalog : Catalog) (count : Nat) (input : Json) : Except String TypeId := do
  let id ← catalog.natural (← catalog.field input "type_id" "ABI type") "ABI type"
  unless id < count do throw s!"ABI query references invalid type {id}"
  return id

private def extra (catalog : Catalog) (count : Nat) (input : Json) : Except String (Array TypeId) := do
  (← catalog.array (← catalog.field input "extra_argument_types" "ABI query") "extra types").mapM (ty catalog count)

private def group (catalog : Catalog) (keys : List String) (read : Json → String → Decode A) :
    Decode (Except String (Array A)) := do
  try
    let values ← catalog.array (← path catalog catalog.root keys) "ABI query table"
    return .ok (← values.mapIdxM fun index value => read value s!"ABI queries[{index}]")
  catch reason => return .error reason

private def instanceRow (catalog : Catalog) (tables : AbiTables) (count : Nat) (input : Json) (location : String) : Decode InstanceAbiQuery := do
  environment catalog input
  let callee ← InstanceReader.read catalog count input location
  return ⟨callee, ← extra catalog count input, reference catalog tables input ["abi_query"]⟩

private def descriptor (input : String) : Except String Miri.Interpreter.ForeignItems.SignatureType :=
  match input with
  | "unit" => pure .unit | "usize" => pure .usize | "isize" => pure .isize
  | "i32" => pure .i32 | "u32" => pure .u32 | "pointer" => pure .pointer
  | "unitPointer" => pure .unitPointer | "alignment" => pure .alignment | "never" => pure .never
  | "u64" => pure .u64 | "u8" => pure .u8 | "bool" => pure .bool
  | "byteSlice" => pure .byteSlice | "functionPointer" => pure .functionPointer
  | _ => throw "unknown compiler shim type descriptor"

private def shim (catalog : Catalog) (tables : AbiTables) (count : Nat) (input : Json) (location : String) : Decode ShimAbiQuery := do
  environment catalog input
  let signature ← catalog.field input "signature" location
  let convention ← match ← catalog.string (← catalog.field signature "calling_convention" location) location with
    | "C" => pure Miri.ABI.CanonAbi.C | "Rust" => pure .Rust
    | _ => throw "unknown compiler shim convention"
  unless !(← catalog.boolean (← catalog.field signature "c_variadic" location) location) do
    throw "variadic compiler shim recipe unsupported"
  let args ← (← catalog.array (← catalog.field signature "arguments" location) location).mapM fun arg => do
    descriptor (← catalog.string arg location)
  let result ← descriptor (← catalog.string (← catalog.field signature "return" location) location)
  let abi := do
    let query ← catalog.field input "query" location
    catalog.requireSupported query location
    let inputs ← catalog.array (← catalog.field query "input_types" location) location
    unless inputs.size == args.size do throw "compiler shim type count mismatch"
    for input in inputs do let _ ← ty catalog count input; pure ()
    let _ ← ty catalog count (← catalog.field query "output_type" location)
    reference catalog tables input ["query","abi_query"]
  return ⟨⟨convention,args,result⟩,abi⟩

private def namedShim (catalog : Catalog) (tables : AbiTables) (input : Json) (location : String) : Decode NamedShimAbiQuery := do
  let name ← catalog.string (← catalog.field input "name" location) location
  environment catalog (← catalog.field input "recipe" location)
  return ⟨name, reference catalog tables input ["recipe","query","abi_query"]⟩

private def pointer (catalog : Catalog) (tables : AbiTables) (count : Nat) (input : Json) (_ : String) : Decode PointerAbiQuery := do
  environment catalog input
  return ⟨← ty catalog count input, ← extra catalog count input, reference catalog tables input ["abi_query"]⟩

private def signature (catalog : Catalog) (tables : AbiTables) (count : Nat) (input : Json) (location : String) : Decode SignatureAbiQuery := do
  environment catalog input
  let signature ← catalog.field input "signature" location
  let inputs ← (← catalog.array (← catalog.field signature "inputs" location) location).mapM fun input => do
    let value ← ty catalog count input
    pure value
  let output ← ty catalog count (← catalog.field signature "output" location)
  let externAbi ← FunctionReader.externAbi catalog (← catalog.field signature "abi" location) location
  let safety ← catalog.field signature "safety" location
  catalog.requireSupported safety location
  let safety ← match ← catalog.string (← catalog.field safety "kind" location) location with
    | "safe" => pure Safety.Safe | "unsafe" => pure .Unsafe
    | _ => throw "unknown helper signature safety"
  return ⟨inputs,output,externAbi,safety,
    ← catalog.boolean (← catalog.field signature "c_variadic" location) location,
    ← catalog.boolean (← catalog.field input "splatted" location) location,
    reference catalog tables input ["abi_query"]⟩

def read (catalog : Catalog) (tables : AbiTables) (count : Nat) : Decode AbiQueries := do
  return {
    instances := ← group catalog ["compiler_instance_abis"] (instanceRow catalog tables count)
    shims := ← group catalog ["compiler_shim_abis"] (shim catalog tables count)
    namedShims := ← group catalog ["compiler_named_shim_abis"] (namedShim catalog tables)
    pointers := ← group catalog ["compiler_function_facts","pointer_abis"] (pointer catalog tables count)
    signatures := ← group catalog ["compiler_function_facts","helper_signatures"] (signature catalog tables count) }

end AbiQueryReader
end Miri.Input.Reader
