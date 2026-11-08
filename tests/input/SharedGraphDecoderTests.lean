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
  let failure := ref (id + 2)
  let parent := Json.mkObj [("child", ref id)]
  let nodes := (nodes.push failure).push parent
  let catalog ← must (set catalog "nodes" (.arr nodes))
  let source ← must (set original "shared_payloads" catalog)
  let source ← must (set source "shared_a" (ref id))
  let source ← must (set source "shared_b" (ref (id + 1)))
  let source ← must (set source "shared_c" (ref (id + 1)))
  match decodeJson source.compress, decodeRuntimeJson source.compress with
  | .error full, .error runtime =>
    unless full == runtime do
      throw (IO.userError s!"shared invalid reference diagnostic differs: {full} / {runtime}")
  | _, _ => throw (IO.userError "shared invalid reference must fail both importers")
  IO.println "SharedGraphDecoderTests: shared invalid references are rejected before executable input construction"
