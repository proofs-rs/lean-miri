import Miri.Input
import Miri.Input.CompilerNativeSignatures
import Miri.Input.CompilerThreadLocal

/-! Finite decoder/provider checks on mutations of fresh compiler exports.
Manifest cases retain separate baselines, exact obligations and demanded query
failures. This does not execute MIR or certify completeness of query roles. -/
open Lean Miri.Input Miri.Interpreter
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def read (dir file : String) : IO DecodeResult := do
  must (decodeJson (← IO.FS.readFile (dir ++ "/" ++ file)))
private def arr (value : Json) (key : String) : Except String (Array Json) :=
  (value.getObjVal? key).bind Json.getArr?
private def getAt (values : Array A) (index : Nat) : Except String A :=
  match values[index]? with | some value => pure value | none => .error "manifest query row absent"

def main (args : List String) : IO Unit := do
  let some dir := args.head? | throw (IO.userError "fresh-export case manifest directory required")
  let manifest ← must (Json.parse (← IO.FS.readFile (dir ++ "/cases.json")))
  let mut count := 0
  for row in ← must (arr manifest "cases") do
    let name ← must (row.getObjValAs? String "file")
    -- Producer/query failure is rejected before any execution input exists,
    -- independently of whether an unrelated root would demand the query.
    discard <| read dir (← must (row.getObjValAs? String "baseline"))
    let source ← IO.FS.readFile (dir ++ "/" ++ name)
    match decodeJson source, decodeRuntimeJson source with
    | .error full, .error runtime =>
      check (full == runtime) s!"query failure diagnostics differ: {name}"
    | _, _ => throw (IO.userError s!"failed catalog input was accepted: {name}")
    count := count + 1
  IO.println s!"catalog failures: {count} rejected at both decoder boundaries; no MIR equivalence claim"
