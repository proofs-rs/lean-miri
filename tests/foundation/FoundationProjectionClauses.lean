import Miri.Frontend.FoundationGenericEnvironment
import Miri.Frontend.FoundationProjectionClauses
open Lean Miri.Frontend.Foundation
private def checked {α : Type} (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def failure {α : Type} (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported projection accepted")
def main (paths : List String) : IO Unit := do
  let [finitePath,compilerPath] := paths | throw (IO.userError "expected finite/compiler projection fixtures")
  let document ← checked (Json.parse (← IO.FS.readFile finitePath) >>= decode)
  let some body := document.bodies.find? (fun body =>
    let definition := (body.getObjValAs? Nat "definition").toOption
    match definition.bind (fun id => document.definitions[id]?) with
    | some row => (row.getObjValAs? String "path").toOption == some "identity"
    | none => false) | throw (IO.userError "identity body absent")
  let environment ← checked (body.getObjVal? "environment")
  let flatEnvironment ← checked (flattenEnvironment document environment)
  let clauses ← checked (flatEnvironment.getObjValAs? (Array Json) "clauses")
  let some projection := clauses.find? (fun clause =>
    (clause.getObjValAs? String "kind").toOption == some "projection")
    | throw (IO.userError "genuine FnOnce Output projection absent")
  let parsed ← checked (projectionClauseSource document projection)
  let some pointerRow := document.types.find? (fun row =>
    ((row.getObjVal? "shape" >>= fun shape => shape.getObjValAs? String "kind").toOption == some "function_pointer"))
    | throw (IO.userError "source FnPtr absent")
  let pointerId ← checked (pointerRow.getObjValAs? Nat "type_id")
  let pointer ← checked (instantiate #[] #[] (← checked (typeExpr document pointerId)))
  let types := #[some pointer]
  let _ ← checked (checkProjectionClause document types #[none] projection)
  let _ ← checked (checkFunctionPointerFnTrait document parsed.parentTrait pointer #[.tuple #[]])
  let compiler ← checked (Json.parse (← IO.FS.readFile compilerPath))
  let actualTypes ← checked (compiler.getObjValAs? (Array Json) "types")
  unless actualTypes.any (fun row => (row.getObjValAs? String "display").toOption == some "fn() -> u8") do
    throw (IO.userError "compiler FnOnce specialization pointer absent")
  failure (checkProjectionClause document #[] #[] projection)
  failure (checkProjectionClause document types #[none] (projection.setObjVal! "term"
    (Json.mkObj [("kind",toJson "type"),("type",toJson pointerId)])))
  failure (projectionClauseSource document (projection.setObjVal! "bound_variables" (toJson #[Json.null])))
  failure (projectionClauseSource document (projection.setObjVal! "arguments" (toJson (#[] : Array Json))))
  let args ← checked (projection.getObjValAs? (Array Json) "arguments")
  failure (checkProjectionClause document types #[none] (projection.setObjVal! "arguments" (toJson args.reverse)))
  failure (projectionClauseSource document (projection.setObjVal! "parent_trait" (toJson parsed.definition)))
  IO.println "projection clause: exact FnOnce source identity/ordered args and FnPtr Output hold; wrong binder/parent/order/arity/Output and missing arguments reject"
