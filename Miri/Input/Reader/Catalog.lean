import Lean

namespace Miri.Input.Reader
open Lean

private def marker : String := "$lean_miri_shared_ref"

structure Catalog where
  private mk ::
  nodes : Array Json
  /-- ID-indexed table view used for typed extraction. -/
  root : Json
  /-- Transport order used by producer-authored diagnostic source paths. -/
  sourceRoot : Json

private def reference (value : Json) (path : String) : Except String (Option Nat) := do
  let .obj fields := value | return none
  unless fields.contains marker do return none
  unless fields.toList.length == 1 do throw s!"{path}: shared reference has extra fields"
  return some (← (← value.getObjVal? marker).getNat?)

private partial def validate (value : Json) (total limit : Nat) (path : String) : Except String Unit := do
  if let some id ← reference value path then
    if id >= total then throw s!"{path}: shared ID {id} is outside table of size {total}"
    if id >= limit then throw s!"{path}: shared ID {id} must precede node {limit}"
    return
  match value with
  | .arr values =>
    for (value, index) in values.toList.zipIdx do
      validate value total limit s!"{path}[{index}]"
  | .obj fields =>
    for (key, value) in fields.toList do
      validate value total limit s!"{path}.{key}"
  | _ => pure ()

private def inspectNodes (nodes : Array Json) (input : Json) (path : String) : Except String Json := do
  match ← reference input path with
  | none => return input
  | some id =>
    let some value := nodes[id]? | throw s!"{path}: invalid shared ID {id}"
    return value

private def indexTable (nodes : Array Json) (root : Json) (table key : String) : Except String Json := do
  let .obj fields := root | throw "$: expected document object"
  let .ok input := root.getObjVal? table | return root
  let path := s!"$.{table}"
  let values ← (← inspectNodes nodes input path).getArr?
  let mut slots : Array (Option Json) := Array.replicate values.size none
  for (value,index) in values.toList.zipIdx do
    let record ← inspectNodes nodes value s!"{path}[{index}]"
    let id ← (← inspectNodes nodes (← record.getObjVal? key) path).getNat?
    if bound : id < slots.size then
      unless slots[id].isNone do throw s!"{path}: duplicate {key} {id}"
      slots := slots.set id (some value) bound
    else throw s!"{path}: {key} {id} outside table of size {slots.size}"
  let values ← slots.mapIdxM fun id slot =>
    match slot with
    | some value => pure value
    | none => throw s!"{path}: {key} {id} absent from dense table"
  return Json.mkObj (fields.toList.map fun (name,value) =>
    (name, if name == table then Json.arr values else value))

def Catalog.parse (input : Json) : Except String Catalog := do
  let .obj fields := input | throw "$: expected document object"
  if fields.contains marker then throw "$: document root must not be a shared reference"
  let catalog ← input.getObjVal? "shared_payloads"
  let .obj catalogFields := catalog | throw "$.shared_payloads: expected catalog object"
  unless catalogFields.toList.length == 2 && catalogFields.contains "schema_version" &&
      catalogFields.contains "nodes" do throw "$.shared_payloads: invalid catalog fields"
  unless (← (← catalog.getObjVal? "schema_version").getNat?) == 2 do
    throw "$.shared_payloads: unsupported schema version"
  let nodes ← (← catalog.getObjVal? "nodes").getArr?
  for (node, index) in nodes.toList.zipIdx do
    let path := s!"$.shared_payloads.nodes[{index}]"
    if (← reference node path).isSome then throw s!"{path}: node root must not be a reference"
    validate node nodes.size index path
  let root := Json.mkObj (fields.toList.filter (fun entry => entry.1 != "shared_payloads"))
  validate root nodes.size nodes.size "$"
  let sourceRoot := root
  let root ← indexTable nodes root "types" "type_id"
  let root ← indexTable nodes root "allocations" "allocation_id"
  let root ← indexTable nodes root "instances" "instance_id"
  return ⟨nodes, root, sourceRoot⟩

def Catalog.input (catalog : Catalog) : Except String Json := do
  let .obj fields := catalog.root | throw "$: expected catalog document object"
  return Json.mkObj (("shared_payloads", Json.mkObj [
    ("schema_version", toJson (2 : Nat)), ("nodes", Json.arr catalog.nodes)]) :: fields.toList)

def Catalog.sharedId? (_catalog : Catalog) (input : Json) (path : String) : Except String (Option Nat) :=
  reference input path

-- Exporter nodes have concrete roots, so a field read needs one table access.
def Catalog.inspect (catalog : Catalog) (input : Json) (path : String) : Except String Json := do
  inspectNodes catalog.nodes input path

def Catalog.field (catalog : Catalog) (input : Json) (key path : String) : Except String Json := do
  ((← catalog.inspect input path).getObjVal? key).mapError (fun error => s!"{path}.{key}: {error}")

def Catalog.optionalField (catalog : Catalog) (input : Json) (key path : String) :
    Except String (Option Json) := do
  let value ← catalog.inspect input path
  let .obj _ := value | throw s!"{path}: expected object"
  return (value.getObjVal? key).toOption

def Catalog.array (catalog : Catalog) (input : Json) (path : String) : Except String (Array Json) := do
  (← catalog.inspect input path).getArr?

def Catalog.string (catalog : Catalog) (input : Json) (path : String) : Except String String := do
  (← catalog.inspect input path).getStr?

def Catalog.natural (catalog : Catalog) (input : Json) (path : String) : Except String Nat := do
  (← catalog.inspect input path).getNat?

def Catalog.boolean (catalog : Catalog) (input : Json) (path : String) : Except String Bool := do
  (← catalog.inspect input path).getBool?

def Catalog.requireSupported (catalog : Catalog) (input : Json) (path : String) : Except String Unit := do
  unless (← catalog.string (← catalog.field input "status" path) path) == "supported" do
    throw s!"{path}: compiler payload is unavailable"

end Miri.Input.Reader
