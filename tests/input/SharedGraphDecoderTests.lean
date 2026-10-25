import Miri.Input.Decoder

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: (fields.toList.filter (fun item => item.1 != key))))

private def ref (id : Nat) : Json :=
  Json.mkObj [("$lean_miri_shared_ref", toJson id)]

def main (args : List String) : IO Unit := do
  let path ← match args with
    | path :: _ => pure path
    | _ => throw (IO.userError "expected current exporter fixture")
  let original ← must (Json.parse (← IO.FS.readFile path))
  let catalog ← must (original.getObjVal? "shared_payloads")
  let nodes ← must ((← must (catalog.getObjVal? "nodes")).getArr?)
  let id := nodes.size
  let failure := Json.mkObj [("status", toJson "unsupported"), ("kind", toJson "shared_graph_regression")]
  let parent := Json.mkObj [("child", ref id)]
  let nodes := (nodes.push failure).push parent
  let catalog ← must (set catalog "nodes" (.arr nodes))
  let source ← must (set original "shared_payloads" catalog)
  let source ← must (set source "shared_a" (ref id))
  let source ← must (set source "shared_b" (ref (id + 1)))
  let source ← must (set source "shared_c" (ref (id + 1)))
  let full ← must (decodeJson source.compress)
  let runtime ← must (decodeRuntimeJson source.compress)
  let expected := #["$.shared_a.status", "$.shared_b.child.status", "$.shared_c.child.status"]
  for label in expected do
    for issues in #[full.document.obligations, runtime.document.obligations] do
      unless (issues.filter (fun issue => issue.path == label)).size == 1 do
        throw (IO.userError s!"shared diagnostic missing, duplicated, or rebased incorrectly: {label}")
  unless full.document.obligations == runtime.document.obligations do
    throw (IO.userError "full/runtime diagnostics differ on repeated shared nodes")
  unless !full.document.sharedNodes.isEmpty &&
      full.document.sharedNodes.size == runtime.document.sharedNodes.size do
    throw (IO.userError "shared nodes lost between full and runtime decode")
  IO.println "SharedGraphDecoderTests: repeated diagnostics retain each occurrence path"
