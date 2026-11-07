import MiriTests.Input.SharedPayloads
import Miri.Input.Reader.TargetLayout
import Miri.Input.RuntimeMetadata

open Lean Miri.Input

private def must (value : Except ε α) [ToString ε] : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError (toString reason))

private def set (value : Json) (key : String) (child : Json) : Except String Json :=
  match value with
  | .obj fields => .ok (.obj (fields.insert key child))
  | _ => .error "expected target object"

def main (args : List String) : IO Unit := do
  for path in args do
    let wire ← must (Json.parse (← IO.FS.readFile path))
    let catalog ← must (Reader.Catalog.parse wire)
    let target ← must (catalog.field catalog.root "runtime_target_data_layout" "target")
    let resolved ← must (SharedPayloads.resolveCatalog wire)
    let oracle ← must (resolved.getObjVal? "runtime_target_data_layout")
    let _ : Reader.JsonFields := catalog.jsonFields
    unless Reader.TargetLayout.importTarget target == RuntimeMetadata.importTarget oracle do
      throw (IO.userError "typed target layout changed")
    for (key,value) in #[
        ("i64_align_bytes", toJson (0 : Nat)),
        ("pointer_width_bits", toJson (128 : Nat)),
        ("object_size_bound_bytes", toJson (0 : Nat)),
        ("endian", toJson "unknown")] do
      let target ← must (set (← must (catalog.inspect target "target")) key value)
      let oracle ← must (set oracle key value)
      let actual := Reader.TargetLayout.importTarget target
      let expected := RuntimeMetadata.importTarget oracle
      unless actual == expected && !actual.isOk do
        throw (IO.userError s!"target validation changed: {key}")
  IO.println "target layout IDs: PASS"
