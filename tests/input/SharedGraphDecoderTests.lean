import Miri.Input.Decoder

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: (fields.toList.filter (fun item => item.1 != key))))

def main (args : List String) : IO Unit := do
  let path ← match args with
    | path :: _ => pure path
    | _ => throw (IO.userError "expected current exporter fixture")
  let original ← must (Json.parse (← IO.FS.readFile path))
  let catalog ← must (original.getObjVal? "semantic_tables")
  let nodes ← must ((← must (catalog.getObjVal? "generic_args")).getArr?)
  let id := nodes.size
  let failure := Json.arr #[Json.mkObj [("kind", .str "lifetime"), ("value", toJson (2^100 : Nat))]]
  let parent := Json.arr #[Json.mkObj [("generic_args", toJson id)]]
  let nodes := (nodes.push failure).push parent
  let catalog ← must (set catalog "generic_args" (.arr nodes))
  let source ← must (set original "semantic_tables" catalog)
  let source ← must (set source "shared_a" (Json.mkObj [("generic_args", toJson id)]))
  let source ← must (set source "shared_b" (Json.mkObj [("generic_args", toJson (id + 1))]))
  let source ← must (set source "shared_c" (Json.mkObj [("generic_args", toJson (id + 1))]))
  match decodeJson source.compress, decodeRuntimeJson source.compress with
  | .error full, .error runtime =>
    unless full == runtime do
      throw (IO.userError s!"shared invalid reference diagnostic differs: {full} / {runtime}")
  | _, _ => throw (IO.userError "shared invalid reference must fail both importers")
  IO.println "SharedGraphDecoderTests: shared invalid references are rejected before executable input construction"
