import Miri.Frontend.FoundationGenericEnvironment
import Miri.Frontend.FoundationProjectionClauses
import Miri.Frontend.FoundationObligations
open Lean Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected actual catch_unwind source")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let candidates ← checked <| document.bodies.filterM fun body => do
    let definition ← body.getObjValAs? Nat "definition"
    let some row := document.definitions[definition]? | throw "source body definition missing"
    return (← row.getObjValAs? String "path") == "std::panic::catch_unwind"
  let [body] := candidates.toList | throw (IO.userError "expected one explicit catch template")
  let definition ← checked (body.getObjValAs? Nat "definition")
  let some row := document.definitions[definition]? | throw (IO.userError "catch definition missing")
  unless (← checked (row.getObjValAs? String "path")) == "std::panic::catch_unwind" do
    throw (IO.userError "not actual catch source")
  let environment ← checked (body.getObjVal? "environment")
  let flatEnvironment ← checked (flattenEnvironment document environment)
  let clauses ← checked (flatEnvironment.getObjValAs? (Array Json) "clauses")
  let projections := clauses.filter fun clause => (clause.getObjValAs? String "kind").toOption == some "projection"
  let [projection] := projections.toList | throw (IO.userError "catch source Output equality absent")
  let result := ConcreteType.primitive "uint" "u8"
  let pointer := ConcreteType.functionPointer #[] result "safe" "rust" false
  let types := #[some pointer,some result]
  let _ ← checked (checkProjectionClause document types #[none,none] projection)
  -- A solved equality does not discharge Sized/UnwindSafe/other parent demands.
  match checkEnvironment document types #[none,none] environment with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "catch parent environment unexpectedly discharged")
  IO.println "actual catch_unwind generic source retained; FnPtr Output equality checked; complete parent obligations remain unsupported"
