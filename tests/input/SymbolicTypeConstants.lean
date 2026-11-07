import Miri.Input.Reader.Generics
import Miri.Input.LowerMIR

open Lean Miri Miri.Input
private def parameter : Json := Json.mkObj [
  ("kind",.str "parameter"),("status",.str "incomplete"),
  ("index",toJson (0 : Nat)),("name",.str "N"),
  ("declared_type",Json.mkObj [("status",.str "unknown"),
    ("reason",.str "ConstKind::Param has no declared type")])]
private def read (input : Json) : Except String MIR.TypeConst := do
  let catalog ← Reader.Catalog.parse (Json.mkObj [("shared_payloads",Json.mkObj [
    ("schema_version",toJson (2 : Nat)),("nodes",.arr #[input])])])
  let (id,state) ← (Reader.GenericReader.constant catalog 0
    (Json.mkObj [("$lean_miri_shared_ref",toJson (0 : Nat))]) "parameter").run
      (Reader.MIRReader.initial 1 {})
  let some value := state.compiler.typeConstants[id]? | throw "missing type constant"
  pure value
private def set (input : Json) (key : String) (value : Json) : Json :=
  match input with
  | .obj fields => Json.mkObj ((key,value) :: fields.toList.filter (fun row => row.1 != key))
  | _ => input
private def must {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)
private def check (condition : Bool) (reason : String) : IO Unit :=
  unless condition do throw (IO.userError reason)

def main : IO Unit := do
  let actual ← must (read parameter)
  check (actual == .Param 0 "N" none) "symbolic parameter became a value or lost its identity"
  -- Independent pre-table lowering accepts this exact symbolic source term.
  let context : LowerContext := {typeIds := #[], scalarSizes := #[]}
  let (id,legacy) ← must (lowerCompilerTypeConst context {}
    (← must (context.decodeCompilerValue parameter)))
  check (legacy.typeConstants[id]? == some actual) "symbolic term differs from the old lowering oracle"
  check (!(read (set parameter "status" (.str "unsupported"))).isOk)
    "unsupported parameter was silently accepted"
  check (!(read (set parameter "index" (.str "invalid"))).isOk)
    "malformed parameter index was accepted"
  check (!(read (set parameter "declared_type" (Json.mkObj [("status",.str "invented")]))).isOk)
    "invalid declared type metadata was accepted"
  check (!(read (set parameter "kind" (.str "value"))).isOk)
    "incomplete concrete value was accepted"
  IO.println "symbolic incomplete ConstKind::Param preserves independent old semantics and rejects invalid values: PASS"
