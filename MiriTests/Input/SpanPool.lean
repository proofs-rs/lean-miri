import Miri.Input.LowerMIR
import Miri.Input.TableCore

open Miri Miri.Input

private def span : SourceSpanData := {
  lo := 3, hi := 8,
  start := ⟨1, 2⟩, «end» := ⟨1, 7⟩, context := "ctx", file := 0 }

private def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)

def main : IO Unit := do
  let fields := "\"is_dummy\":false,\"lo\":3,\"hi\":8,\"start\":{\"line\":1,\"column\":2}," ++
    "\"end\":{\"line\":1,\"column\":7},\"file\":0,\"ctxt\":"
  let text := "{ " ++ fields ++ "\"#7\\n\\\"macro\\\"\"}"
  let .ok decoded := JsonReader.run DecoderValues.parseSourceSpan text
    | throw (IO.userError "source context string rejected")
  check (decoded.context == "#7\n\"macro\"") "source context diagnostic text changed"
  let legacy := "{" ++ fields ++ "{\"status\":\"debug_payload\",\"rustc_debug\":\"#7\"}}"
  check (!(JsonReader.run DecoderValues.parseSourceSpan legacy).isOk)
    "source context object accepted instead of a string"
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
