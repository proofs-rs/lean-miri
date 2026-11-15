import Miri.Frontend.Foundation
import Miri.MIR.Syntax

/-! Retained source lifetime binders and a strict codegen-erasure view.
Only one ordinary function-signature lifetime binder is handled. Its source
identities remain in Document.source; a temporary type-table view replaces
validated innermost bound reference/dyn lifetimes with Erased. Escaping, nested,
canonical, type/const binders and unknown type forms reject. This is not a
lifetime inference or outlives solver. -/
namespace Miri.Frontend.Foundation
open Lean

private def regionKind (document : Document) (source : Json) : Except String MIR.BoundRegionKind := do
  match ← source.getObjValAs? String "kind" with
  | "anonymous" => return .Anon
  | "closure_environment" => return .ClosureEnv
  | "named_for_printing" =>
    let name ← source.getObjValAs? String "name"
    unless !name.isEmpty do throw "empty bound-region printing name"
    return .NamedForPrinting name
  | "named" =>
    let id ← source.getObjValAs? Nat "definition"
    let some definition := document.definitions[id]? | throw "bound-region definition absent"
    unless (← definition.getObjValAs? Nat "definition_id") == id do
      throw "bound-region definition table identity mismatch"
    unless (← definition.getObjValAs? String "kind") == "LifetimeParam" do
      throw "bound-region named definition is not a lifetime parameter"
    return .Named id
  | _ => throw "bound-region kind unsupported"

/-- Read every captured variable, preserving named source definition references.
Missing binder material is an error, never an implicit empty binder. -/
def signatureBoundVariables (document : Document) (signature : Json) :
    Except String (Array MIR.BoundVariableKind) := do
  (← signature.getObjValAs? (Array Json) "bound_variables").mapM fun entry => do
    unless (← entry.getObjValAs? String "kind") == "region" do
      throw "signature type/const binder unsupported"
    return .Region (← regionKind document (← entry.getObjVal? "region_kind"))

private def erasedRegion (document : Document) (variables : Array MIR.BoundVariableKind)
    (source : Json) : Except String Json := do
  if let .ok name := source.getStr? then
    unless name == "static" || name == "erased" do throw "signature free/unknown region unsupported"
    return source
  unless (← source.getObjValAs? String "kind") == "bound" do
    throw "signature region form unsupported"
  unless (← source.getObjValAs? Nat "debruijn") == 0 do
    throw "escaping/nested signature bound region unsupported"
  let slot ← source.getObjValAs? Nat "variable"
  let some (.Region expected) := variables[slot]? | throw "signature bound region variable absent"
  unless (← regionKind document (← source.getObjVal? "region_kind")) == expected do
    throw "signature bound region identity mismatch"
  return toJson "erased"

private def eraseType (document : Document) (variables : Array MIR.BoundVariableKind)
    (fuel : Nat) (path : Array Nat) (rows : Array Json) (id : Nat) : Except String (Array Json) := do
  let .succ fuel := fuel | throw "signature type erasure traversal exhausted"
  unless !path.contains id do throw "cyclic signature type erasure reference"
  -- Validate every occurrence against retained source, not a row already
  -- erased along a different binder path.
  let some row := document.types[id]? | throw "signature type erasure row absent"
  unless (← row.getObjValAs? Nat "type_id") == id do throw "signature type table identity mismatch"
  let shape ← row.getObjVal? "shape"
  let kind ← shape.getObjValAs? String "kind"
  let path := path.push id
  let children (rows : Array Json) (ids : Array Nat) : Except String (Array Json) :=
    ids.foldlM (fun rows child => eraseType document variables fuel path rows child) rows
  match kind with
  | "bool" | "char" | "int" | "uint" | "float" | "never" | "str" | "param" => return rows
  | "raw_pointer" => children rows #[← shape.getObjValAs? Nat "pointee"]
  | "adt" =>
    let mut ids := #[]
    for argument in (← shape.getObjValAs? (Array Json) "arguments") do
      unless (← argument.getObjValAs? String "kind") == "type" do
        throw "signature nominal non-type argument unsupported"
      ids := ids.push (← argument.getObjValAs? Nat "type")
    children rows ids
  | "array" => children rows #[← shape.getObjValAs? Nat "element"]
  | "tuple" => children rows (← shape.getObjValAs? (Array Nat) "elements")
  | "pattern_type" =>
    let pattern ← shape.getObjVal? "pattern"
    unless (← pattern.getObjValAs? String "kind") == "not_null" do
      throw "signature constrained type pattern unsupported"
    children rows #[← shape.getObjValAs? Nat "base"]
  | "reference" =>
    let region ← erasedRegion document variables (← shape.getObjVal? "region")
    let rewritten := row.setObjVal! "shape" (shape.setObjVal! "region" region)
    let rows := rows.mapIdx fun index original => if index == id then rewritten else original
    children rows #[← shape.getObjValAs? Nat "pointee"]
  | "dynamic" =>
    let region ← erasedRegion document variables (← shape.getObjVal? "region")
    let rewritten := row.setObjVal! "shape" (shape.setObjVal! "region" region)
    let rows := rows.mapIdx fun index original => if index == id then rewritten else original
    let mut ids := #[]
    for predicate in (← shape.getObjValAs? (Array Json) "predicates") do
      unless (← predicate.getObjValAs? (Array Json) "bound_variables").isEmpty do
        throw "nested existential binder in signature unsupported"
      match ← predicate.getObjValAs? String "kind" with
      | "trait" | "projection" =>
        for argument in (← predicate.getObjValAs? (Array Json) "arguments") do
          unless (← argument.getObjValAs? String "kind") == "type" do
            throw "signature existential generic argument unsupported"
          ids := ids.push (← argument.getObjValAs? Nat "type")
        if (← predicate.getObjValAs? String "kind") == "projection" then
          let term ← predicate.getObjVal? "term"
          unless (← term.getObjValAs? String "kind") == "type" do
            throw "signature existential projection term unsupported"
          ids := ids.push (← term.getObjValAs? Nat "type")
      | "auto_trait" => pure ()
      | _ => throw "signature existential predicate unsupported"
    children rows ids
  | "function_pointer" =>
    let signature ← shape.getObjVal? "signature"
    unless (← signature.getObjValAs? (Array Json) "bound_variables").isEmpty do
      throw "nested function-pointer binder context unsupported"
    let inputs ← signature.getObjValAs? (Array Nat) "inputs"
    let output ← signature.getObjValAs? Nat "output"
    -- An empty inner binder may contain Static/Erased regions, but it must
    -- not capture an outer bound region at a different de Bruijn depth.
    (inputs.push output).foldlM (fun rows child =>
      eraseType document #[] fuel path rows child) rows
  | _ => throw "signature binder type shape unsupported"
termination_by fuel

/-- Instantiate the captured ordinary FnSig binder with erased regions in pure
Lean. The returned view preserves original source JSON and source type indices;
only reachable, validated reference/dyn region fields in `types` change. Normal
source parsing still rejects unbound region objects outside this operation. -/
def eraseSignatureBinder (document : Document) (signature : Json) : Except String Document := do
  let variables ← signatureBoundVariables document signature
  if variables.isEmpty then return document
  let inputs ← signature.getObjValAs? (Array Nat) "inputs"
  let output ← signature.getObjValAs? Nat "output"
  let rows ← (inputs.push output).foldlM (fun rows id =>
    eraseType document variables (document.types.size + 1) #[] rows id) document.types
  return { document with types := rows }

end Miri.Frontend.Foundation
