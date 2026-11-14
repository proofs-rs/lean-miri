import Miri.Input.GenericMaterialCodec

open Miri.Input

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: GenericMaterialStreaming NESTED.json")
  let source ← IO.FS.readFile path
  let parser := JsonReader.object (none, none) fun (templates, sentinel) key => do
    match key with
    | "templates" => pure (some (← JsonReader.array GenericMaterialCodec.decodeTemplate), sentinel)
    | "sentinel" => pure (templates, some (← JsonReader.natural))
    | _ => JsonReader.fail "unexpected nested generic test field"
  match JsonReader.run parser source with
  | .error error => throw (IO.userError error)
  | .ok (some templates, some 43) =>
    unless templates.size ≥ 2 do throw (IO.userError "nested generic fixture needs two templates")
    IO.println "nested generic templates preserve following fields and document boundary"
    pure 0
  | _ => throw (IO.userError "nested generic template parser lost following fields")
