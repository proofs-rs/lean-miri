import Miri.Frontend.FoundationObligations

open Lean Miri.Frontend.Foundation

private def demand (d : Document) (expected : String) : Except String ConcreteType := do
  let some body := d.bodies[0]? | throw "missing requested body"
  let typeArgs := if expected == "concrete" then #[] else #[some (.primitive "uint" "u8"), none]
  let constArgs := if expected == "array" then #[none, some 7] else #[]
  let environment ← body.getObjVal? "environment"
  checkEnvironment d typeArgs constArgs environment
  if expected != "concrete" &&
      (checkEnvironment d #[] #[] environment).isOk then
    throw "unbound environment unexpectedly accepted"
  let locals ← body.getObjValAs? (Array Nat) "locals"
  let some result := locals[0]? | throw "missing return local"
  let source ← typeExpr d result
  if expected != "concrete" && (instantiate #[] #[] source).isOk then
    throw "unbound generic parameters unexpectedly resolved"
  instantiate typeArgs constArgs source

def main (args : List String) : IO Unit := do
  let path :: expected :: _ := args | throw (IO.userError "usage: FoundationMaterial JSON identity|array")
  let contents ← IO.FS.readFile path
  let json ← match Json.parse contents with
    | .ok j => pure j
    | .error e => throw (IO.userError e)
  let d ← match decode json with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let value ← match demand d expected with
    | .ok v => pure v
    | .error e => throw (IO.userError e)
  match expected, value with
  | "identity", .primitive "uint" "u8" => pure ()
  | "array", .array (.primitive "uint" "u8") 7 => pure ()
  | "concrete", .array (.primitive "uint" "u16") 3 => pure ()
  | _, _ => throw (IO.userError s!"wrong requested instantiation: {repr value}")
  IO.println s!"foundation demand: {expected} ok"
