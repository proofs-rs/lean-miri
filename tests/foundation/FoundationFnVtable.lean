import Miri.Frontend.FoundationFnVtable
open Lean Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error e => throw (IO.userError e)
private def rejects (value : Except String α) : IO Unit :=
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "malformed Fn source accepted")

private def replaceDeclaration (source : FnVtableDeclarations) (id : Nat) (row : Json) :
    Except String FnVtableDeclarations := do
  let some index := source.declarations.findIdx? (fun value => (value.getObjValAs? Nat "definition").toOption == some id)
    | throw "missing source declaration"
  if h : index < source.declarations.size then
    return {source with declarations := source.declarations.set index row h}
  else throw "source declaration index absent"

def main (paths : List String) : IO Unit := do
  let [path, compilerPath] := paths | throw (IO.userError "expected fresh dynamic source and schema12 vtable oracle")
  let document ← checked (Json.parse (← IO.FS.readFile path))
  let source ← checked (readFnVtableDeclarations document)
  for (kind, count) in [("fn",6),("fn_mut",5),("fn_once",4)] do
    let plan ← checked (fnVtableCandidates source (← checked (fnSourceRoot source kind)))
    unless plan.slots.size == count do throw (IO.userError "Fn source candidate slot count mismatch")
  let principal ← checked (fnSourceRoot source "fn")
  let plan ← checked (fnVtableCandidates source principal)
  let compiler ← checked (Json.parse (← IO.FS.readFile compilerPath))
  let queries ← checked (compiler.getObjValAs? (Array Json) "compiler_vtable_queries")
  unless queries.size == 1 do throw (IO.userError "compiler oracle requires one concrete vtable")
  let some query := queries[0]? | throw (IO.userError "compiler vtable oracle absent")
  let metadata ← checked (query.getObjVal? "vtable_metadata")
  let entries ← checked (metadata.getObjValAs? (Array Json) "entries")
  let instances ← checked (compiler.getObjValAs? (Array Json) "instances")
  let definitions ← checked (compiler.getObjValAs? (Array Json) "definitions")
  unless entries.size == plan.slots.size do throw (IO.userError "compiler vtable slot count differs")
  let mut methodNames := #[]
  let mut shimKinds := #[]
  for (slot, entry) in plan.slots.zip entries do
    let kind ← checked (entry.getObjValAs? String "kind")
    match slot with
    | .dropInPlace => unless kind == "drop_in_place_null" do throw (IO.userError "compiler drop source differs")
    | .size => unless kind == "size_bytes" do throw (IO.userError "compiler size slot differs")
    | .alignment => unless kind == "align_bytes" do throw (IO.userError "compiler alignment slot differs")
    | .methodOrVacant _ method name =>
      unless kind == "method" do throw (IO.userError "compiler concrete Fn method is vacant")
      let id ← checked (entry.getObjValAs? Nat "instance_id")
      let some target := instances[id]? | throw (IO.userError "compiler method instance absent")
      let defId ← checked (target.getObjValAs? Nat "def_id")
      let some expected := definitions[defId]? | throw (IO.userError "compiler method definition absent")
      let some actual := source.definitions[method]? | throw (IO.userError "source method definition absent")
      unless (← checked (actual.getObjValAs? Nat "crate_index")) == (← checked (expected.getObjValAs? Nat "crate")) &&
          (← checked (actual.getObjValAs? Nat "index")) == (← checked (expected.getObjValAs? Nat "index")) do
        throw (IO.userError "compiler vtable source method identity/order differs")
      let instanceKind ← checked (target.getObjVal? "instance_kind")
      shimKinds := shimKinds.push (← checked (instanceKind.getObjValAs? String "shim_kind"))
      methodNames := methodNames.push name
  unless methodNames == #["call_once","call_mut","call"] && shimKinds == #["vtable","fn_pointer","fn_pointer"] do
    throw (IO.userError "compiler Fn shim source boundary changed")
  -- Source plans do not create these compiler-selected shim instances.
  rejects (readFnVtableDeclarations (document.setObjVal! "fn_vtable_source" Json.null))
  rejects (fnVtableCandidates source source.definitions.size)
  let row ← checked (fnSourceDeclaration source principal)
  let stripped := row.setObjVal! "associated_items" (toJson (#[] : Array Json))
  rejects (do fnVtableCandidates (← replaceDeclaration source principal stripped) principal)
  let stripped := row.setObjVal! "super_clauses" (toJson (#[] : Array Json))
  rejects (do fnVtableCandidates (← replaceDeclaration source principal stripped) principal)
  let items ← checked (row.getObjValAs? (Array Json) "associated_items")
  let some item := items[0]? | throw (IO.userError "Fn method source absent")
  let method ← checked (item.getObjVal? "method")
  for changed in [method.setObjVal! "final" (toJson true),
      method.setObjVal! "own_clauses" (toJson (#["Self: Sized"] : Array String))] do
    let altered := row.setObjVal! "associated_items" (toJson (#[item.setObjVal! "method" changed] : Array Json))
    rejects (do fnVtableCandidates (← replaceDeclaration source principal altered) principal)
  let markers ← checked (source.declarations.filterM fun value => return (← value.getObjValAs? String "lang_item") == "meta_sized")
  let some marker := markers[0]? | throw (IO.userError "MetaSized source absent")
  let markerId ← checked (marker.getObjValAs? Nat "definition")
  let selfArgument := Json.mkObj [("kind",toJson "type"),("type",Json.mkObj [("kind",toJson "param"),("index",toJson (0 : Nat))])]
  let cycle := Json.mkObj [("kind",toJson "trait"),("definition",toJson markerId),
    ("arguments",toJson (#[selfArgument] : Array Json)),("polarity",toJson "Positive"),("bound_variables",toJson (#[] : Array Json))]
  let altered := marker.setObjVal! "super_clauses" (toJson (#[cycle] : Array Json))
  match fnVtableCandidates (← checked (replaceDeclaration source markerId altered)) principal with
  | .error "cyclic Fn supertrait source" => pure ()
  | .error e => throw (IO.userError s!"unexpected cycle outcome: {e}")
  | .ok _ => throw (IO.userError "cyclic Fn declaration source accepted")
  let duplicate := {source with declarations := source.declarations.push row}
  rejects (fnSourceDeclaration duplicate principal)
  IO.println "Fn declaration candidates: source DFS matches 6 compiler slots/method identities; concrete shim resolution remains separate"
