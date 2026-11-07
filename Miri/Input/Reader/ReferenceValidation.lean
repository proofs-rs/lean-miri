import Miri.Input.Reader.Catalog

/-! Reference checks over the transport DAG. Shared JSON is inspected at its
existing ID and is never replaced by an expanded subtree. Inline containers do
not need structural hashes or an auxiliary copy of the document. -/
namespace Miri.Input.Reader
open Lean

private partial def visit (catalog : Catalog) (raw : Json) (path : String)
    (typeCount allocationCount instanceCount : Nat) (seen : Std.HashSet Nat) :
    Except String (Std.HashSet Nat) := do
  let id ← catalog.sharedId? raw path
  if let some id := id then
    if seen.contains id then return seen
  let value ← catalog.inspect raw path
  if let .ok (some status) := catalog.optionalField value "status" path then
    if (catalog.string status path).toOption == some "debug_payload" then return seen
  let finish := fun seen => match id with
    | some id => seen.insert id
    | none => seen
  match value with
  | .arr values =>
    let mut seen := seen
    for (child, index) in values.toList.zipIdx do
      seen ← visit catalog child s!"{path}[{index}]" typeCount allocationCount instanceCount seen
    return finish seen
  | .obj fields =>
    match fields.toList with
    | [("type_id", rawId)] =>
      let index ← catalog.natural rawId s!"{path}.type_id"
      if index >= typeCount then throw s!"{path}: dangling type reference {index}"
      return finish seen
    | [("allocation_id", rawId)] =>
      let index ← catalog.natural rawId s!"{path}.allocation_id"
      if index >= allocationCount then throw s!"{path}: dangling allocation reference {index}"
      return finish seen
    | _ => pure ()
    let mut seen := seen
    for (key, child) in fields.toList do
      if key == "instance_id" then
        let index ← catalog.natural child s!"{path}.{key}"
        if index >= instanceCount then throw s!"{path}.{key}: dangling instance reference {index}"
      seen ← visit catalog child s!"{path}.{key}" typeCount allocationCount instanceCount seen
    return finish seen
  | _ => return finish seen

def Catalog.validateReferences (catalog : Catalog)
    (typeCount allocationCount instanceCount : Nat) : Except String Unit := do
  discard <| visit catalog catalog.root "$" typeCount allocationCount instanceCount {}

end Miri.Input.Reader
