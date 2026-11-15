import Miri.Frontend.FoundationGenericEnvironment
import Miri.Frontend.FoundationObligations
import Miri.Frontend.FoundationOutlives
import Miri.Input.Decoder

open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Check a finite `T: 'static` request at unit and match rustc's independently
resolved unit instance from the same source. This is not a general lifetime or
trait solver comparison. Erased/reference/pointer signatures remain unknown. -/
def main (paths : List String) : IO Unit := do
  let [foundationPath, compilerPath] := paths | throw (IO.userError "expected finite generic and ordinary unit-wrapper exports")
  let document ← checked (Json.parse (← IO.FS.readFile foundationPath) >>= decode)
  let some body := document.bodies[0]? | throw (IO.userError "generic source body absent")
  let definition ← checked (body.getObjValAs? Nat "definition")
  let environment ← checked (body.getObjVal? "environment")
  let flatEnvironment ← checked (flattenEnvironment document environment)
  let clauses ← checked (flatEnvironment.getObjValAs? (Array Json) "clauses")
  unless clauses.any (fun clause =>
      (clause.getObjValAs? String "kind").toOption == some "type_outlives" &&
      (clause.getObjValAs? String "region").toOption == some "static") do
    throw (IO.userError "source static outlives predicate absent")
  checked (checkEnvironment document #[some (.tuple #[])] #[none] environment)
  let locals ← checked ((← checked (body.getObjValAs? (Array Nat) "locals")).mapM fun id => do
    instantiate #[some (.tuple #[])] #[none] (← typeExpr document id))
  unless locals.all (fun ty => match ty with | .tuple fields => fields.isEmpty | _ => false) do
    throw (IO.userError "unit type-outlives substitution changed")
  let some sourceDefinition := document.definitions[definition]? | throw (IO.userError "source definition absent")
  let crateIndex ← checked (sourceDefinition.getObjValAs? Nat "crate_index")
  let index ← checked (sourceDefinition.getObjValAs? Nat "index")
  let compiler ← checked (Input.decodeJson (← IO.FS.readFile compilerPath))
  let doc := compiler.document
  let some actual := doc.instances.find? (fun node =>
    match node.definitionId.bind (doc.definitions[·]?) with
    | some row => row.crateIndex == crateIndex && row.index == index
    | none => false) | throw (IO.userError "rustc unit instance for exact source DefId absent")
  let [.Type actualUnit] := actual.genericArgs.toList | throw (IO.userError "rustc instance generic arguments differ")
  unless actualUnit == doc.queries.primitives.unit && actual.bodyId.isSome do
    throw (IO.userError "rustc did not resolve the same executable unit instance")
  for ty in #[ConcreteType.tuple #[], .primitive "uint" "u8", .array (.primitive "int" "i16") 3] do
    let _ ← checked (checkStaticOutlives ty "static")
  for ty in #[ConcreteType.pointer "reference_erased_const" (.primitive "uint" "u8"),
      .pointer "raw_pointer_const" (.primitive "uint" "u8"),
      .functionPointer #[] (.tuple #[]) "safe" "rust" false] do
    match checkStaticOutlives ty "static" with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "unanalysed lifetime/pointer outlives assigned static")
  match checkStaticOutlives (.tuple #[]) "erased" with
  | .error "unsupported type-outlives region" => pure ()
  | _ => throw (IO.userError "erased region treated as static")
  IO.println "foundation outlives: source T:static at unit matches fresh compiler instance; unanalysed regions/shapes reject"
