import Miri.Input.GenericSubstitution
import Lean.Data.Json.Parser
import Lean.Data.Json.Printer

open Lean Miri.Input.GenericSubstitution

private def readSort (value : Json) : Except String ArgSort := do
  match ← (← value.getObjVal? "sort").getStr? with
  | "type" => pure .type | "region" => pure .region
  | "constant" => pure .constant | "aggregate" => pure .aggregate
  | _ => throw "unknown generic material sort"

private def decode : Nat → Json → Except String Miri.Input.GenericSubstitution.Term
  | 0, _ => .error "generic material parser depth exhausted"
  | fuel + 1, value => do
    let natural (key : String) := do (← value.getObjVal? key).getNat?
    let string (key : String) := do (← value.getObjVal? key).getStr?
    match ← string "kind" with
    | "parameter" => return .parameter (← readSort value) (← natural "index")
    | "bound" => do
      let raw ← value.getObjVal? "index"
      let index : Miri.MIR.BoundVarIndexKind ← if raw == .null then pure .Canonical
        else do
          let n ← raw.getNat?
          pure (.Bound n)
      return .bound (← readSort value) index (← natural "variable") (← string "identity")
    | "placeholder" => return .placeholder (← readSort value) (← natural "universe") (← natural "variable") (← string "identity")
    | "inference" => return .inference (← readSort value) (← natural "variable")
    | "atom" => return .atom (← readSort value) (← string "tag") (← string "payload")
    | "node" => do
      let elements ← (← value.getObjVal? "children").getArr?
      return .node (← readSort value) (← string "tag") (← string "payload")
        (← elements.mapM (decode fuel))
    | "binder" => do
      let variables ← (← value.getObjVal? "variables").getArr?
      return .binder (← variables.mapM Json.getStr?) (← decode fuel (← value.getObjVal? "value"))
    | other => throw s!"unknown generic material node {other}"

def main (args : List String) : IO UInt32 := do
  let [path] := args | throw (IO.userError "usage: CompareGenericSubstitution ORACLE.json")
  let text ← IO.FS.readFile path
  let result : Except String Nat := do
    let rows ← (← Json.parse text).getArr?
    unless rows.size ≥ 10 do throw "generic material comparison needs at least ten real rustc cases"
    for row in rows do
      let template ← decode 256 (← row.getObjVal? "template")
      let arguments ← (← (← row.getObjVal? "arguments").getArr?).mapM (decode 256)
      let expected ← decode 256 (← row.getObjVal? "expected")
      let actual ← instantiate 256 arguments template
      unless actual == expected do
        throw s!"rustc generic substitution mismatch: Lean={repr actual}; rustc={repr expected}"
    pure rows.size
  match result with
  | .error error => throw (IO.userError error)
  | .ok count => IO.println s!"{count} fresh rustc/Lean early substitution comparisons passed"
  pure 0
