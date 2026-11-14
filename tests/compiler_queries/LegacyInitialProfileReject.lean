import Miri.Input.Decoder

open Miri

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def checkRejected (text : String) : IO Unit := do
  match Input.decodeJson text with
  | .error message =>
    unless message.contains "dedicated initial-profile decoder" do
      throw (IO.userError s!"wrong rejection: {message}")
  | .ok _ => throw (IO.userError "legacy decoder accepted an initial compiler profile")

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a valid current compiler document")
  let text ← IO.FS.readFile path
  let _ ← must (Input.decodeJson text)
  let document ← must (Lean.Json.parse text)
  let fields := (← must document.getObj?).toArray
  unless fields.all (fun field => field.1 != "compiler_initial_global_snapshot" &&
      field.1 != "compiler_initial_ctfe_roots") do
    throw (IO.userError "base document already contains an initial profile")
  let controls : Array (String × Lean.Json) := #[
    ("compiler_initial_global_snapshot", Lean.Json.mkObj []),
    ("compiler_initial_ctfe_roots", Lean.Json.arr #[]),
    ("compiler_initial_global_snapshot", Lean.Json.null),
    ("compiler_initial_ctfe_roots", Lean.Json.null)]
  for control in controls do
    checkRejected (Lean.Json.mkObj ((fields.push control).toList)).compress
  IO.println "PASS legacy decoder explicitly rejects both initial-profile fields, including malformed payloads"
