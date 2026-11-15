import Miri.Frontend.FoundationObligations
import Miri.Frontend.FoundationTraitClaims

open Lean Miri.Frontend.Foundation

private def rejected (result : Except String α) : IO Unit := do
  match result with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "unsupported local trait obligation accepted")

def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected fresh local trait JSON")
  let document ← match Json.parse (← IO.FS.readFile path) >>= decode with
    | .ok d => pure d
    | .error e => throw (IO.userError e)
  let some body := document.bodies[0]? | throw (IO.userError "missing trait fixture body")
  let environment ← IO.ofExcept (body.getObjVal? "environment")
  for name in #["u8", "u32"] do
    match checkEnvironment document #[some (.primitive "uint" name)] #[none] environment with
    | .ok _ => pure ()
    | .error e => throw (IO.userError e)
  rejected (checkEnvironment document #[some (.primitive "uint" "u16")] #[none] environment)
  rejected (checkEnvironment document #[some (.array (.primitive "uint" "u8") 3)] #[none] environment)
  let some row := document.definitions.find? (fun d => (d.getObjVal? "local_trait").isOk)
    | throw (IO.userError "missing local trait source")
  let source ← match row.getObjVal? "local_trait" with
    | .ok v => pure v
    | .error e => throw (IO.userError e)
  let headers ← match source.getObjValAs? (Array Json) "implementations" with
    | .ok v => pure v
    | .error e => throw (IO.userError e)
  let self := ConcreteType.primitive "uint" "u8"
  for changed in #[source.setObjVal! "complete_impl_headers" (toJson false),
      source.setObjVal! "implementations" (toJson (headers ++ headers)),
      source.setObjVal! "super_clauses" (toJson (#[Json.null] : Array Json))] do
    rejected (localTraitClaim (row.setObjVal! "local_trait" changed) self)
  rejected (localTraitClaim (row.setObjVal! "local_trait" Json.null) self)
  IO.println "local trait source headers: two positive, two negative demands and four malformed controls passed"
