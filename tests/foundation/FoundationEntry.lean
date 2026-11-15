import Miri.Frontend.FoundationEntry
open Lean Miri.Frontend.Foundation

private def fixture (entry : String) (start : String := "null") : Except String EntrySelection := do
  entrySelection (← Json.parse ("{\"definitions\":[{}],\"entry_selection\":{\"compiler_entry\":" ++ entry ++ ",\"start_lang_item\":" ++ start ++ "}}"))

def main : IO Unit := do
  match fixture "null" with
  | .ok value => unless value.compilerEntry.isNone && value.startLangItem.isNone do throw (IO.userError "entry absence changed")
  | .error e => throw (IO.userError e)
  match fixture "{\"definition\":0,\"kind\":\"rustc_main\",\"sigpipe\":255}" "0" with
  | .ok value => unless value.compilerEntry == some ⟨0,255⟩ && value.startLangItem == some 0 do throw (IO.userError "entry selection changed")
  | .error e => throw (IO.userError e)
  for input in [fixture "null" "1", fixture "{\"definition\":1,\"kind\":\"rustc_main\",\"sigpipe\":0}",
      fixture "{\"definition\":0,\"kind\":\"unknown\",\"sigpipe\":0}",
      fixture "{\"definition\":0,\"kind\":\"rustc_main\",\"sigpipe\":256}"] do
    match input with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "malformed entry accepted")
  IO.println "foundation entry selection: 2 source cases and 4 rejection controls passed"
