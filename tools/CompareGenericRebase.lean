import Miri.Input.GenericArgsCodec
import Miri.Input.GenericRebase
import Lean.Data.Json.Printer

open Miri.Input

private def check (row : Lean.Json) : Except String Nat := do
  let rawArgs ← row.getObjVal? "args"
  let rawExpected ← row.getObjVal? "rebased_args"
  let args ← JsonReader.run GenericArgsCodec.decode rawArgs.compress
  let expected ← JsonReader.run GenericArgsCodec.decode rawExpected.compress
  let concrete ← (← row.getObjVal? "concrete_type").getNat?
  let mut count := 0
  -- The algebra cancels the trait-prefix truncation and concatenation. Check
  -- every possible nonempty trait prefix against the independent rustc result;
  -- this includes the actual generics.count without inferring it from the result.
  for parentCount in [1:args.size + 1] do
    let result ← GenericRebase.virtualSelf args parentCount concrete
    unless result == expected do throw s!"rustc rebase mismatch at prefix {parentCount}"
    count := count + 1
  return count

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: CompareGenericRebase ORACLE.json")
  let source ← IO.FS.readFile path
  let result : Except String Nat := do
    let json ← Lean.Json.parse source
    let rows ← json.getArr?
    unless rows.size > 0 do throw "no real virtual rebase oracle rows"
    let mut count := 0
    for row in rows do count := count + (← check row)
    pure count
  match result with
  | .error error => throw (IO.userError error)
  | .ok count => IO.println s!"{count} rustc/Lean generic rebase prefix comparisons passed"
  return 0
