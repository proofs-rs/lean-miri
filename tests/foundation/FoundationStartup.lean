import Miri.Frontend.FoundationStartup

open Lean Miri.Frontend.Foundation

private def unwrap (value : Except String α) : IO α := do
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def rejected (value : Except String α) : IO Unit := do
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "incomplete/unsupported startup source accepted")

private def withMaterial (document : Document) (material : Json) : Document :=
  { document with source := document.source.setObjVal! "startup_material" material }

def main (paths : List String) : IO Unit := do
  let [path, expectedPath, noCorePath] := paths
    | throw (IO.userError "expected foundation, compact schema12 reference, no_core JSON paths")
  let document ← unwrap (Json.parse (← IO.FS.readFile path) >>= decode)
  let expected ← unwrap (Json.parse (← IO.FS.readFile expectedPath))
  let startup ← unwrap (startupOfDocument document)
  unless !startup.noCore do throw (IO.userError "ordinary crate marked no_core")
  let some (definition, available) := startup.coreEscapeDefault
    | throw (IO.userError "core startup definition absent")
  let some identity := document.definitions[definition]?
    | throw (IO.userError "core startup identity out of bounds")
  unless (← unwrap (identity.getObjValAs? Nat "crate_index")) ==
      (← unwrap (expected.getObjValAs? Nat "crate_index")) &&
      (← unwrap (identity.getObjValAs? Nat "index")) ==
      (← unwrap (expected.getObjValAs? Nat "index")) &&
      available == (← unwrap (expected.getObjValAs? Bool "mir_available")) do
    throw (IO.userError "pure startup lookup disagrees with genuine schema12 compiler query")
  let material ← unwrap (document.source.getObjVal? "startup_material")
  rejected (startupOfDocument (withMaterial document (material.setObjVal! "modules" (toJson (#[] : Array Json)))))
  rejected (startupOfDocument (withMaterial document (material.setObjVal! "crates" (toJson (#[] : Array Json)))))
  rejected (resolveStartupPath document "core" "ascii" "unsupported")
  let modules ← unwrap (material.getObjValAs? (Array Json) "modules")
  let mut changed := #[]
  let mut missingMir := #[]
  for node in modules do
    let children ← unwrap (node.getObjValAs? (Array Json) "children")
    let mut reordered := #[]
    let mut incomplete := #[]
    for child in children do
      if (child.getObjValAs? (Option Nat) "definition").toOption == some (some definition) &&
          (child.getObjValAs? String "name").toOption == some "escape_default" then
        reordered := reordered.push (child.setObjVal! "namespace" (toJson "type"))
        incomplete := incomplete.push (child.setObjVal! "mir_available" Json.null)
      else incomplete := incomplete.push child
      reordered := reordered.push child
    changed := changed.push (node.setObjVal! "children" (toJson reordered))
    missingMir := missingMir.push (node.setObjVal! "children" (toJson incomplete))
  let reordered := withMaterial document (material.setObjVal! "modules" (toJson changed))
  unless (← unwrap (startupOfDocument reordered)) == startup do
    throw (IO.userError "startup namespace filter did not skip wrong-namespace child")
  rejected (startupOfDocument (withMaterial document (material.setObjVal! "modules" (toJson missingMir))))
  let noCore ← unwrap (Json.parse (← IO.FS.readFile noCorePath) >>= decode)
  unless (← unwrap (startupOfDocument noCore)) ==
      ⟨(← unwrap (expected.getObjValAs? Bool "no_core_comparison")), none⟩ do
    throw (IO.userError "genuine no_core source did not skip startup resolution")
  IO.println "startup source graph: genuine compiler identity/MIR comparison, no_core, namespace and four rejection controls passed"
