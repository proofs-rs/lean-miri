import Miri.Frontend.FoundationInstance
import Miri.Input.Model.Catalogs

/-! Source attributes to fixed-interpreter runtime metadata for ordinary root
items. `Instance::print` and `FmtPrinter::print_path_with_generic_args` supply the
restricted diagnostic formatting below; no mangled symbol is invented. Frame
crate IDs/names and definition attributes are finite material, while physical
and ABI identities are computed by the demand-local registries. -/
namespace Miri.Frontend.Foundation
open Lean

/-- Preserve compiler crate identity/name material, rejecting missing joins. -/
def frameMetadataOfSource (document : Document) : Except String Input.Catalog.FrameMetadata := do
  let source ← document.source.getObjVal? "frame_metadata"
  let localCrate ← source.getObjValAs? Nat "local_crate"
  let mut crates : Array (Nat × String) := #[]
  for row in (← source.getObjValAs? (Array Json) "crates") do
    let id ← row.getObjValAs? Nat "crate"
    unless id < 2^32 && !(crates.any (·.1 == id)) do throw "invalid or duplicate frame crate identity"
    crates := crates.push (id, ← row.getObjValAs? String "name")
  unless crates.any (·.1 == localCrate) do throw "local frame crate identity absent"
  for definition in document.definitions do
    let crateId ← definition.getObjValAs? Nat "crate_index"
    unless crates.any (·.1 == crateId) do throw "definition frame crate identity absent"
  return ⟨localCrate, crates⟩

/-- Restricted pinned Rust type spelling for source item diagnostics. This
covers startup's unit, thin raw pointers and ordinary Rust function pointers;
unknown regions, arrays and other structural forms remain errors. -/
def concreteRuntimeDisplay (ty : ConcreteType) : Except String String := go 64 ty
where
  go (fuel : Nat) (ty : ConcreteType) : Except String String := do
    let .succ fuel := fuel | throw "runtime type display depth exhausted"
    match ty with
    | .primitive "bool" "" => pure "bool"
    | .primitive "char" "" => pure "char"
    | .primitive "uint" name =>
      if name ∈ ["u8", "u16", "u32", "u64", "u128", "usize"] then pure name
      else throw "unsupported runtime unsigned type display"
    | .primitive "int" name =>
      if name ∈ ["i8", "i16", "i32", "i64", "i128", "isize"] then pure name
      else throw "unsupported runtime signed type display"
    | .tuple elements =>
      unless elements.isEmpty do throw "runtime tuple display unsupported"
      pure "()"
    | .pointer kind pointee =>
      let pointerPrefix ← match kind with
        | "raw_pointer_const" => pure "*const "
        | "raw_pointer_mut" => pure "*mut "
        | _ => throw "runtime reference/pointer display unsupported"
      pure (pointerPrefix ++ (← go fuel pointee))
    | .functionPointer inputs output safety abi variadic =>
      unless abi == "rust" && !variadic do throw "runtime function-pointer ABI display unsupported"
      unless safety == "safe" || safety == "unsafe" do throw "runtime function-pointer safety display unsupported"
      let inputs ← inputs.mapM (go fuel)
      let output ← go fuel output
      pure ((if safety == "unsafe" then "unsafe " else "") ++ "fn(" ++
        String.intercalate ", " inputs.toList ++ ")" ++ (if output == "()" then "" else " -> " ++ output))
    | _ => throw "unsupported runtime instance argument display"

/-- Runtime facts for a source-backed Item identity. The source definition path
and explicit concrete type arguments determine its name. External free functions
use the same source/attribute checks and preserved frame crate table as local
functions. Declaration-selected associated methods use their checked resolver.
Symbol mangling is not implemented:
`symbolName = none` retains the genuine absent-query boundary for later demands. -/
def runtimeInstanceOfHeader (document : Document) (definitionId : Nat)
    (arguments : Array ItemArgument) (sourceHeader : Json) (node : Input.InstanceNode) : Except String Input.Catalog.RuntimeInstance := do
  let some definition := document.definitions[definitionId]? | throw "runtime source definition absent"
  unless node.instanceKind == .Item definitionId &&
      node.definitionId == some definitionId do throw "runtime source instance identity mismatch"
  let frame ← frameMetadataOfSource document
  let crateIndex ← definition.getObjValAs? Nat "crate_index"
  unless frame.crates.any (·.1 == crateIndex) do throw "runtime source frame crate absent"
  let kind ← definition.getObjValAs? String "kind"
  unless kind == "fn" do throw "runtime header requires ordinary free function source"
  unless (← sourceHeader.getObjValAs? Nat "definition") == definitionId do
    throw "runtime header source definition mismatch"
  let facts ← sourceHeader.getObjVal? "runtime_source"
  let root ← facts.getObjValAs? Bool "is_local_root"
  let some name ← facts.getObjValAs? (Option String) "item_name"
    | throw "runtime instance item name absent"
  let path ← definition.getObjValAs? String "path"
  unless path == name || path.endsWith ("::" ++ name) do
    throw "runtime instance definition path/item-name mismatch"
  unless root == (crateIndex == frame.localCrate && path == name) do
    throw "runtime instance local-root source identity mismatch"
  let arguments ← arguments.mapM fun argument => do
    match argument with
    | .type ty => concreteRuntimeDisplay ty
    | .constant _ => throw "runtime const argument display unsupported"
  let display := path ++ (if arguments.isEmpty then "" else "::<" ++ String.intercalate ", " arguments.toList ++ ">")
  let attrs ← sourceHeader.getObjVal? "function_attributes"
  let track ← attrs.getObjValAs? Bool "track_caller"
  let foreign ← attrs.getObjValAs? Bool "is_foreign"
  unless !track && !foreign && !(← attrs.getObjValAs? Bool "is_drop_glue") do
    throw "runtime instance requires unadjusted nonforeign item"
  unless !(← facts.getObjValAs? Bool "rustc_intrinsic") do
    throw "runtime instance intrinsic definition unsupported"
  let inlineAttribute ← facts.getObjValAs? String "inline"
  unless inlineAttribute ∈ ["none", "hint", "always", "never"] do
    throw "runtime instance inline attribute unsupported"
  -- Foundation export rejects nonempty source target_features before capture.
  let targetFeatures ← facts.getObjValAs? (Array Json) "target_features"
  unless targetFeatures.isEmpty do throw "runtime instance target features unsupported"
  let symbol ← facts.getObjValAs? (Option String) "codegen_symbol_name"
  return {
    instanceId := node.id
    requiresCallerLocation := track
    display
    inlineNever := inlineAttribute == "never"
    targetFeatures := #[]
    isForeignItem := foreign
    isClosureLike := false -- source kind is exactly an ordinary free function
    intrinsicMetadata := some none
    itemName := some name
    codegenSymbolName := some symbol
    symbolName := none
  }

end Miri.Frontend.Foundation
