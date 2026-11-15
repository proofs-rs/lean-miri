import Miri.Frontend.FoundationFnAbi
import Miri.Frontend.FoundationPhysicalRegistry
import Miri.Frontend.FoundationInstance
import Miri.Frontend.FoundationObligations
import Miri.Frontend.FoundationSignatureBinder
import Miri.Frontend.FoundationRegionErasure
import Miri.Frontend.FoundationGenericEnvironment
import Miri.Frontend.FoundationItemResolution

/-! Demand-time FnAbi from one declared generic source signature. This query
never reads MIR locals, instructions, promoted bodies or required constants and
does not establish that a function body can execute. It keeps signature binders,
generic obligations and source attributes separate from the physical ABI query.
No compiler FnAbi or per-substitution answer table is consumed. -/
namespace Miri.Frontend.Foundation
open Lean

private def sourceHeader (d : Document) (definition : Nat) : Except String Json := do
  let bodies ← d.bodies.filterM fun source => return (← source.getObjValAs? Nat "definition") == definition
  let rows ← match d.source.getObjVal? "source_function_signatures" with
    | .ok value => fromJson? value
    | .error _ => pure (#[] : Array Json)
  let headers ← rows.filterM fun source => return (← source.getObjValAs? Nat "definition") == definition
  unless bodies.size ≤ 1 && headers.size ≤ 1 do throw "duplicate function signature source owner"
  match bodies[0]?, headers[0]? with
  | none, none => throw "function signature source unavailable"
  | some body, none => return body
  | none, some header => return header
  | some body, some header =>
    for key in #["environment", "signature", "function_attributes"] do
      unless (← body.getObjVal? key) == (← header.getObjVal? key) do throw "conflicting function signature source"
    return header

/-- Parse-time declaration reader; does not inspect MIR locals or instructions. -/
def functionHeaderSource (d : Document) (definition : Nat) : Except String Json :=
  sourceHeader d definition

private def substitutions (d : Document) (source : Json) (arguments : Array ItemArgument) :
    Except String (Array (Option ConcreteType) × Array (Option Nat)) := do
  let sourceEnvironment ← source.getObjVal? "environment"
  let environment ← flattenEnvironment d sourceEnvironment
  let parameters ← environment.getObjValAs? (Array Json) "parameters"
  unless parameters.size == arguments.size do throw "signature generic argument count mismatch"
  let mut types := #[]
  let mut constants := #[]
  for i in [:parameters.size] do
    let some parameter := parameters[i]? | throw "signature parameter absent"
    unless (← parameter.getObjValAs? Nat "index") == i do throw "signature parameter index mismatch"
    let some argument := arguments[i]? | throw "signature argument absent"
    match ← parameter.getObjValAs? String "kind", argument with
    | "type", .type ty => types := types.push (some ty); constants := constants.push none
    | "const", .constant n => types := types.push none; constants := constants.push (some n)
    | _, _ => throw "signature generic argument kind unsupported"
  checkEnvironment d types constants sourceEnvironment
  for parameter in parameters do
    if (← parameter.getObjValAs? String "kind") == "const" then
      let index ← parameter.getObjValAs? Nat "index"
      let ty ← instantiate types constants (← typeExpr d (← parameter.getObjValAs? Nat "type"))
      let .primitive "uint" "usize" := ty | throw "signature const parameter must be usize"
      let some value := constants[index]?.bind id | throw "signature const argument absent"
      unless value < 2 ^ d.target.pointerSizeBits do throw "signature const argument exceeds usize"
  return (types, constants)

private def binding (r : PhysicalTypeRegistry) (ty : ConcreteType) :
    Except String (PhysicalTypeRegistry × AbiTypeBinding) := do
  let (r, id) ← r.intern ty
  let (node, layout) ← r.lookup id
  let expected ← rustAbiLayoutOfDocument r.registry.document ty
  unless layout.sizeBytes == some expected.size && layout.abiAlignBytes == some expected.align do
    throw "signature ABI physical layout disagreement"
  let _ ← r.runtimeLayout id
  return (r, ⟨ty, node.id, node.layoutId⟩)

/-- Compute the ABI of a selected source declaration without requiring its MIR
body. All physical IDs are allocated by the supplied document-local registry. -/
def rustFunctionAbiOfSourceSignatureInRegistry (initial : PhysicalTypeRegistry) (definition : Nat)
    (arguments : Array ItemArgument) : Except String (PhysicalTypeRegistry × Input.FunctionAbi) := do
  let d := initial.registry.document
  let some owner := d.definitions[definition]? | throw "signature definition absent"
  let kind ← owner.getObjValAs? String "kind"
  unless kind == "fn" || (kind == "assoc_fn" && (← sourceInherentItem d definition)) do
    throw "signature ABI requires ordinary function or checked inherent owner"
  let source ← sourceHeader d definition
  let (types, constants) ← substitutions d source arguments
  let signature ← source.getObjVal? "signature"
  let view ← eraseSignatureBinder d signature
  let abi ← signature.getObjVal? "abi"
  unless (← abi.getObjValAs? String "kind") == "rust" && (← abi.getObjVal? "unwind") == Json.null do
    throw "signature ABI requires ordinary Rust convention"
  unless !(← signature.getObjValAs? Bool "c_variadic") do throw "signature variadic ABI unsupported"
  let safety ← signature.getObjValAs? String "safety"
  unless safety == "safe" || safety == "unsafe" do throw "signature safety unsupported"
  let attrs ← source.getObjVal? "function_attributes"
  unless !(← attrs.getObjValAs? Bool "track_caller") && !(← attrs.getObjValAs? Bool "is_foreign") &&
      !(← attrs.getObjValAs? Bool "is_drop_glue") do throw "signature ABI requires unadjusted ordinary item"
  let resolve (id : Nat) : Except String ConcreteType := do
    eraseRegions (← instantiate types constants (← typeExpr view id))
  let output ← resolve (← signature.getObjValAs? Nat "output")
  let (r, result) ← binding initial output
  let mut registry := r
  let mut inputs := #[]
  for id in (← signature.getObjValAs? (Array Nat) "inputs") do
    let (next, input) ← binding registry (← resolve id)
    registry := next
    inputs := inputs.push input
  let unwind ← rustUnwindFactsOfSource d.source source
  let abi ← rustFunctionAbiComponentOfDocument d unwind inputs result
  for argument in abi.arguments.push abi.returnValue do
    if argument.mode.kind == .indirect || argument.mode.kind == .indirectUnsized then
      throw "signature indirect ABI requires MIR attribute deduction"
  return (registry, abi)

def rustFunctionAbiOfSourceSignature (d : Document) (definition : Nat) (arguments : Array ItemArgument) :
    Except String (PhysicalTypeRegistry × Input.FunctionAbi) :=
  rustFunctionAbiOfSourceSignatureInRegistry (PhysicalTypeRegistry.start d) definition arguments

end Miri.Frontend.Foundation
