import Miri.Input.ConstIntegerPrinter

open Lean Miri.Input
def main (args : List String) : IO Unit := do
  let [oracle] := args | throw (IO.userError "expected oracle.json")
  let rows ← match (Json.parse (← IO.FS.readFile oracle)).bind Json.getArr? with
    | .ok value => pure value | .error error => throw (IO.userError error)
  for row in rows do
    let parsed := do
      let bytes ← (← row.getObjVal? "bytes").getNat?
      let raw ← (← row.getObjVal? "raw").getStr?
      let some raw := raw.toNat? | throw "invalid oracle integer"
      let signed ← (← row.getObjVal? "signed").getBool?
      let pointer ← (← row.getObjVal? "pointer").getBool?
      let expected ← (← row.getObjVal? "display").getStr?
      let actual ← ConstIntegerPrinter.scalar signed pointer bytes raw
      unless actual == expected do throw s!"ConstInt differs: {actual} vs {expected}"
    match parsed with | .ok () => pure () | .error error => throw (IO.userError error)
  unless rows.size == 72 do throw (IO.userError "oracle lacks 72 integer cases")
  IO.println "PASS 72 pinned rustc ConstInt format cases including signed MIN/MAX, unsigned MAX, 128-bit and pointer widths"
