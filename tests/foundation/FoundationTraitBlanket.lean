import Miri.Frontend.FoundationObligations
import Miri.Frontend.FoundationTraitClaims

open Lean Miri.Frontend.Foundation

private def unwrap (value : Except String α) : IO α := do
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def requireError (value : Except String α) (diagnostic : String) : IO Unit := do
  match value with
  | .error error => unless error == diagnostic do throw (IO.userError s!"wrong rejection: {error}")
  | .ok _ => throw (IO.userError "ambiguous/unsupported trait blanket accepted")

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh array blanket source JSON")
  let document ← unwrap (Json.parse (← IO.FS.readFile path) >>= decode)
  let some body := document.bodies[0]? | throw (IO.userError "missing marked template")
  let environment ← unwrap (body.getObjVal? "environment")
  let some row := document.definitions.find? (fun row => (row.getObjVal? "local_trait").isOk)
    | throw (IO.userError "missing local blanket source")
  for name in #["u8", "u32"] do
    let _ ← unwrap (checkEnvironment document #[some (.array (.primitive "uint" name) 3)] #[none] environment)
  unless !(← unwrap (localTraitClaim row (.array (.primitive "uint" "u8") 4))) do
    throw (IO.userError "nonmatching array length satisfied local trait")
  let shared := ConcreteType.array (.pointer "reference_static_const" (.primitive "uint" "u8")) 3
  let mutable := ConcreteType.array (.pointer "reference_static_mut" (.primitive "uint" "u8")) 3
  unless (← unwrap (localTraitClaim row shared)) && !(← unwrap (localTraitClaim row mutable)) do
    throw (IO.userError "Copy clause failed to distinguish shared/mutable reference elements")
  let material ← unwrap (row.getObjVal? "local_trait")
  let headers ← unwrap (material.getObjValAs? (Array Json) "implementations")
  let some header := headers[0]? | throw (IO.userError "blanket header absent")
  let index ← unwrap (header.getObjValAs? Nat "index")
  let overlap := header.setObjVal! "index" (toJson (index + 100000))
  let ambiguous := row.setObjVal! "local_trait" (material.setObjVal! "implementations" (toJson (headers.push overlap)))
  requireError (localTraitClaim ambiguous (.array (.primitive "uint" "u8") 3))
    "duplicate matching local trait impls"
  let supertrait := Json.mkObj [("kind", toJson "self_trait"), ("lang_item", toJson "copy"), ("self_parameter", toJson (0 : Nat))]
  let unsupported := row.setObjVal! "local_trait" (material.setObjVal! "super_clauses" (toJson #[supertrait]))
  requireError (localTraitClaim unsupported (.array (.primitive "uint" "u8") 3))
    "unsupported local trait super clause"
  IO.println "array blanket source: primitive/shared positive, length/Copy negative, ambiguity/supertrait rejection passed"
