import Miri.Frontend.FoundationObligations
open Lean Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α := do
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def rejected (value : Except String α) : IO Unit := do
  match value with | .error _ => pure () | .ok _ => throw (IO.userError "unsupported termination selection accepted")
def main (paths : List String) : IO Unit := do
  let [sourcePath,compilerPath,stdPath] := paths | throw (IO.userError "expected source and compiler method identities")
  let document ← checked (Json.parse (← IO.FS.readFile sourcePath) >>= decode)
  let source ← checked (document.source.getObjVal? "termination_source")
  let traitDef ← checked (source.getObjValAs? Nat "definition")
  let result ← checked (sourceTerminationUnitSelection document traitDef (.tuple #[]))
  let some method := document.definitions[result.implementationMethodDefinition]? | throw (IO.userError "selected method absent")
  let references ← checked (Json.parse (← IO.FS.readFile compilerPath) >>= fun j => j.getArr?)
  let key := Json.mkObj [("crate",toJson (← checked (method.getObjValAs? Nat "crate_index"))),("index",toJson (← checked (method.getObjValAs? Nat "index")))]
  let some _ := references.find? (fun row => (row.getObjVal? "identity").toOption == some key)
    | throw (IO.userError "source-selected method differs from actual compiler Item call")
  let headers ← checked (source.getObjValAs? (Array Json) "implementations")
  let some selected := headers.find? (fun h => (h.getObjValAs? Nat "definition").toOption == some result.implementationDefinition)
    | throw (IO.userError "selected header absent")
  let mutate (replacement : Json) := {document with source := document.source.setObjVal! "termination_source" replacement}
  rejected (sourceTerminationUnitSelection document traitDef (.primitive "uint" "u8"))
  rejected (sourceTerminationUnitSelection document document.definitions.size (.tuple #[]))
  rejected (sourceTerminationUnitSelection (mutate (source.setObjVal! "complete_impl_headers" (toJson false))) traitDef (.tuple #[]))
  rejected (sourceTerminationUnitSelection (mutate (source.setObjVal! "implementations" (toJson (headers.push selected)))) traitDef (.tuple #[]))
  let alteredHeaders := fun changed => headers.map (fun h => if (h.getObjValAs? Nat "definition").toOption == some result.implementationDefinition then changed else h)
  for changed in #[selected.setObjVal! "polarity" (toJson "Negative"),
      selected.setObjVal! "clause_count" (toJson (1:Nat)),selected.setObjVal! "final" (toJson false),
      selected.setObjVal! "self_constructor" (Json.mkObj [("kind",toJson "unknown")]),
      selected.setObjVal! "associated_items" (toJson (#[] : Array Json)),
      selected.setObjVal! "parameter_count" (toJson (1:Nat))] do
    rejected (sourceTerminationUnitSelection (mutate (source.setObjVal! "implementations" (toJson (alteredHeaders changed)))) traitDef (.tuple #[]))
  let competitor := headers.map fun h =>
    if (h.getObjValAs? Nat "definition").toOption != some result.implementationDefinition then
      h.setObjVal! "self_constructor" (Json.mkObj [("kind",toJson "tuple"),("arity",toJson (0:Nat))])
    else h
  rejected (sourceTerminationUnitSelection (mutate (source.setObjVal! "implementations" (toJson competitor))) traitDef (.tuple #[]))
  rejected (sourceTerminationUnitSelection (mutate (source.setObjVal! "meta_sized_definition" (toJson document.definitions.size))) traitDef (.tuple #[]))
  let stdDoc ← checked (Json.parse (← IO.FS.readFile stdPath) >>= decode)
  let stdSource ← checked (stdDoc.source.getObjVal? "termination_source")
  let _ ← checked (sourceTerminationUnitSelection stdDoc (← checked (stdSource.getObjValAs? Nat "definition")) (.tuple #[]))
  let mut sawStart := false
  for body in stdDoc.bodies do
    let definition ← checked (body.getObjValAs? Nat "definition")
    let some row := stdDoc.definitions[definition]? | throw (IO.userError "std body definition absent")
    if (← checked (row.getObjValAs? String "path")) == "std::rt::lang_start" then
      checked (checkEnvironment stdDoc #[some (.tuple #[])] #[] (← checked (body.getObjVal? "environment")))
      rejected (checkEnvironment stdDoc #[some (.primitive "uint" "u8")] #[] (← checked (body.getObjVal? "environment")))
      sawStart := true
  unless sawStart do throw (IO.userError "genuine standard start source absent")
  IO.println s!"source unit implementation/method agrees with genuine compiler; {headers.size} complete headers and negative controls passed"
