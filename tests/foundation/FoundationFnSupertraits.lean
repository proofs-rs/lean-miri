import Miri.Frontend.FoundationFnSupertraits
import Miri.Frontend.FoundationObligations
open Lean Miri.Frontend.Foundation

private def checked (value : Except String α) : IO α := do
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejected (value : Except String α) : IO Unit := do
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported Fn entailment source accepted")
private def dynamicSource (document : Document) : Except String (Nat × ExistentialType ConcreteType) := do
  let some id := document.types.findIdx? (fun row =>
      ((row.getObjVal? "shape").bind (fun shape => shape.getObjValAs? String "kind")).toOption == some "dynamic")
    | throw "dynamic source absent"
  let .dynamicObject source ← instantiate #[] #[] (← typeExpr document id) | throw "dynamic source lost"
  return (id,source)
private def withDeclarations (document : Document) (rows : Array Json) : Except String Document := do
  let source ← document.source.getObjVal? "fn_vtable_source"
  return {document with source := document.source.setObjVal! "fn_vtable_source" (source.setObjVal! "declarations" (toJson rows))}

def main (paths : List String) : IO Unit := do
  let [path, oncePath] := paths | throw (IO.userError "expected genuine Fn and FnOnce source JSON")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let (sourceId,source) ← checked (dynamicSource document)
  let declarations ← checked (readFnVtableDeclarations document.source)
  let fnId ← checked (fnSourceRoot declarations "fn")
  let mutId ← checked (fnSourceRoot declarations "fn_mut")
  let onceId ← checked (fnSourceRoot declarations "fn_once")
  unless source.principal == some fnId do throw (IO.userError "fixture principal is not compiler Fn language item")
  for target in #[fnId,mutId,onceId] do
    let _ ← checked (checkSourceExistentialTrait document source target source.arguments)
    let selfArg := Json.mkObj [("kind",toJson "type"),("type",toJson sourceId)]
    let some typeRow := document.types[sourceId]? | throw (IO.userError "source type absent")
    let shape ← checked (typeRow.getObjVal? "shape")
    let predicates ← checked (shape.getObjValAs? (Array Json) "predicates")
    let some principal := predicates[0]? | throw (IO.userError "source principal absent")
    let args ← checked (principal.getObjValAs? (Array Json) "arguments")
    let clause := Json.mkObj [("kind",toJson "trait"),("definition",toJson target),("arguments",toJson (#[selfArg] ++ args))]
    let some contextBody := document.bodies[0]? | throw (IO.userError "source declaration context absent")
    let context ← checked (contextBody.getObjVal? "environment")
    let layers ← checked (context.getObjValAs? (Array Json) "layers")
    let environment := context.setObjVal! "layers" (toJson (layers.mapIdx fun index layer =>
      if index + 1 == layers.size then layer.setObjVal! "clauses" (toJson #[clause]) else layer))
    let _ ← checked (checkEnvironment document #[] #[] environment)
  for autoId in source.autoTraits do
    let _ ← checked (checkSourceExistentialTrait document source autoId #[])
  let some projection := source.projections[0]? | throw (IO.userError "Output equality absent")
  let _ ← checked (checkSourceExistentialProjection document source projection.definition projection.arguments (.primitive "int" "i32"))
  rejected (checkSourceExistentialProjection document source projection.definition projection.arguments (.primitive "int" "i64"))
  rejected (checkSourceExistentialTrait document source onceId #[.tuple #[.primitive "uint" "u8"]])
  rejected (checkSourceExistentialTrait document {source with projections := #[]} onceId source.arguments)
  rejected (checkSourceExistentialTrait document {source with autoTraits := source.autoTraits.push onceId} onceId source.arguments)
  let badProjection := {projection with parentTrait := mutId}
  rejected (checkSourceExistentialTrait document {source with projections := #[badProjection]} onceId source.arguments)
  let rows := declarations.declarations
  let fnRow ← checked (fnSourceDeclaration declarations fnId)
  let edges ← checked (fnRow.getObjValAs? (Array Json) "super_clauses")
  let missing ← checked (edges.filterM fun edge => return (← edge.getObjValAs? Nat "definition") != mutId)
  let unknown := Json.mkObj [("kind",toJson "non_trait"),("source",toJson "unsupported predicate")]
  let badRebase ← checked (edges.mapM fun edge => do
    if (← edge.getObjValAs? Nat "definition") != mutId then return edge
    let args ← edge.getObjValAs? (Array Json) "arguments"
    let some self := args[0]? | throw "Self source absent"
    return edge.setObjVal! "arguments" (toJson #[self,self]))
  let bound ← checked (edges.mapM fun edge => do
    return edge.setObjVal! "bound_variables" (toJson #["unsupported binder"]))
  for changed in #[fnRow.setObjVal! "super_clauses" (toJson missing),
      fnRow.setObjVal! "super_clauses" (toJson (edges.push unknown)),
      fnRow.setObjVal! "super_clauses" (toJson badRebase),
      fnRow.setObjVal! "super_clauses" (toJson bound)] do
    let changedRows ← checked (rows.mapM fun row => do
      return if (← row.getObjValAs? Nat "definition") == fnId then changed else row)
    rejected (checkSourceExistentialTrait (← checked (withDeclarations document changedRows)) source onceId source.arguments)
  let some marker := rows.find? (fun row => (row.getObjValAs? String "lang_item").toOption == some "meta_sized")
    | throw (IO.userError "MetaSized declaration absent")
  let markerId ← checked (marker.getObjValAs? Nat "definition")
  let param := Json.mkObj [("kind",toJson "param"),("index",toJson (0 : Nat))]
  let arg := Json.mkObj [("kind",toJson "type"),("type",param)]
  let cycle := Json.mkObj [("kind",toJson "trait"),("definition",toJson markerId),
    ("arguments",toJson #[arg]),("polarity",toJson "Positive"),("bound_variables",toJson (#[] : Array Json))]
  let cycleRows ← checked (rows.mapM fun row => do
    return if (← row.getObjValAs? Nat "definition") == markerId then
      row.setObjVal! "super_clauses" (toJson #[cycle]) else row)
  rejected (checkSourceExistentialTrait (← checked (withDeclarations document cycleRows)) source onceId source.arguments)
  if let some autoId := source.autoTraits[0]? then
    rejected (checkSourceExistentialTrait document {source with projections := #[]} autoId #[])
    rejected (checkSourceExistentialTrait document {source with autoTraits := source.autoTraits.filter (· != autoId)} autoId #[])
    rejected (checkSourceExistentialTrait document {source with autoTraits := source.autoTraits.push autoId} onceId source.arguments)
  let onceDocument ← checked (Json.parse (← IO.FS.readFile oncePath) >>= decode)
  let (_,onceSource) ← checked (dynamicSource onceDocument)
  let onceDeclarations ← checked (readFnVtableDeclarations onceDocument.source)
  let onceRoot ← checked (fnSourceRoot onceDeclarations "fn_once")
  let fnRoot ← checked (fnSourceRoot onceDeclarations "fn")
  let _ ← checked (checkSourceExistentialTrait onceDocument onceSource onceRoot onceSource.arguments)
  rejected (checkSourceExistentialTrait onceDocument onceSource fnRoot onceSource.arguments)
  IO.println "Fn source supertraits: genuine Fn→FnMut→FnOnce, Output/auto joins, reverse and malformed source controls passed"
