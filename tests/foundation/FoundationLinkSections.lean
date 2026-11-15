import Miri.Frontend.FoundationLinkSections
open Lean Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error e => throw (IO.userError e)

def main (paths : List String) : IO Unit := do
  let (path, mode, legacy) ← match paths with
    | [path, mode] => pure (path,mode,none)
    | [path, mode, legacy] => pure (path,mode,some legacy)
    | _ => throw (IO.userError "expected fresh source JSON and empty/nonempty/library")
  let document ← checked (Json.parse (← IO.FS.readFile path))
  if mode == "library" then
    match sourceLinkSections document with
    | .error "link sections require executable dependency format source" => pure ()
    | .error e => throw (IO.userError s!"unexpected missing executable format: {e}")
    | .ok _ => throw (IO.userError "library yielded executable link sections")
  else
    let selected ← checked (sourceLinkSections document)
    if let some legacy := legacy then
      let compiler ← checked (Json.parse (← IO.FS.readFile legacy))
      let main ← checked (compiler.getObjVal? "compiler_main_queries")
      let expected ← checked (main.getObjValAs? (Array Json) "link_sections")
      let definitions ← checked (compiler.getObjValAs? (Array Json) "definitions")
      unless expected.size == selected.size do throw (IO.userError "compiler section selection count differs")
      for (actual, record) in selected.zip expected do
        let id ← checked (record.getObjValAs? Nat "definition")
        let some identity := definitions[id]? | throw (IO.userError "compiler definition missing")
        unless actual.name == (← checked (record.getObjValAs? String "section")) &&
            actual.crateIndex == (← checked (identity.getObjValAs? Nat "crate")) &&
            actual.definitionIndex == (← checked (identity.getObjValAs? Nat "index")) do
          throw (IO.userError "compiler section source order/identity differs")
    if mode == "empty" then
      unless selected.isEmpty do throw (IO.userError "unexpected selected link section")
      let result ← checked (checkedEmptyLinkSections document)
      unless result.isEmpty do throw (IO.userError "empty source selection changed")
    else
      if mode == "nonempty" then
        unless selected.size == 1 && (selected[0]?).any (fun (row : SourceLinkSection) => row.name == ".finite_test") do
          throw (IO.userError "used source section selection mismatch")
      else
        unless selected.any (fun row => row.crateIndex != 0) do
          throw (IO.userError "linked dependency section source missing")
      match checkedEmptyLinkSections document with
      | .error "selected link section requires source global initializer and allocation identity" => pure ()
      | .error e => throw (IO.userError s!"unexpected global boundary failure: {e}")
      | .ok _ => throw (IO.userError "selected static initializer evidence invented")
    let material ← checked (document.getObjVal? "link_section_material")
    let bad := document.setObjVal! "link_section_material"
      (material.setObjVal! "executable_dependencies" Json.null)
    match sourceLinkSections bad with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "missing executable format accepted")
    let dependencies ← checked (material.getObjValAs? (Array Json) "executable_dependencies")
    if let some row := dependencies[0]? then
      let changed := row.setObjVal! "crate_index" (toJson (dependencies.size + 1))
      if h : 0 < dependencies.size then
        let bad := document.setObjVal! "link_section_material"
          (material.setObjVal! "executable_dependencies" (toJson (dependencies.set 0 changed h)))
        match sourceLinkSections bad with
        | .error _ => pure ()
        | .ok _ => throw (IO.userError "non-dense dependency format accepted")
  IO.println s!"fresh link-section source selection: {mode} passed"
