import Miri.Input.Decoder
open Miri.Input
def main (args : List String) : IO Unit := do
  let [path,expected] := args | throw (IO.userError "expected malformed source and role diagnostic")
  match decodeJson (← IO.FS.readFile path) with
  | .ok _ => throw (IO.userError "malformed compiler body source role was accepted")
  | .error error =>
    unless error.contains expected do throw (IO.userError s!"wrong body role diagnostic: {error}")
    IO.println "PASS malformed compiler body source role rejected"
