import Miri.Input.Decoder

def main (args : List String) : IO Unit := do
  let [positive,malformed] := args | throw (IO.userError "expected valid and missing-raw-field caller source")
  match Miri.Input.decodeJson (← IO.FS.readFile positive) with
  | .error error => throw (IO.userError s!"valid caller source rejected: {error}")
  | .ok _ => pure ()
  match Miri.Input.decodeJson (← IO.FS.readFile malformed) with
  | .ok _ => throw (IO.userError "missing raw Location field accepted")
  | .error error => unless error.contains "ADT source field safety and expression domains differ" do
      throw (IO.userError s!"raw Location field rejected at unrelated boundary: {error}")
  IO.println "PASS missing raw Location field rejected by strict source decoder"
