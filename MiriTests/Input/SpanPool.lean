import Miri.Input.LowerMIR

open Miri Miri.Input

private def span : SourceSpanData := {
  lo := 3, hi := 8,
  start := ⟨1, 2⟩, «end» := ⟨1, 7⟩, context := "ctx", file := 0 }

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main : IO Unit := do
  let tables : CompilerTables := {spans := #[span, span], definitions := #[], typeConstants := #[]}
  for id in #[0, 1] do
    let .ok (reference, after) := lowerCompilerSpan tables ⟨id⟩
      | throw (IO.userError "valid span ID rejected")
    check (reference.id == id) "equal span payloads collapsed distinct IDs"
    check (after.spans == tables.spans) "span lookup changed definitions"
    check (after.definitions == tables.definitions && after.typeConstants == tables.typeConstants)
      "span lookup changed another pool"
  for id in #[2, 999999] do
    check (!(lowerCompilerSpan tables ⟨id⟩).isOk) "out of bounds span accepted"
  IO.println "span IDs preserve definitions and reject out of bounds references"
