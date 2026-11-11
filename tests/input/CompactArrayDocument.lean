import Miri.Input.Decoder

open Lean Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [legacyPath, compactPath] := args | throw (IO.userError "expected unchanged schema-8 and fresh schema-9 inputs")
  let legacyText ← IO.FS.readFile legacyPath
  let legacy ← must (decodeJson legacyText)
  for layout in legacy.document.layouts do
    match layout.fieldOffsetsBytes with
    | .explicit _ => pure ()
    | .arrayFormula .. => throw (IO.userError "legacy fixture no longer has its original dense offsets")
  let compactText ← IO.FS.readFile compactPath
  let compact ← must (decodeJson compactText)
  unless compact.document.layouts.any (fun layout => match layout.fieldOffsetsBytes with
      | .arrayFormula _ _ => true | _ => false) do
    throw (IO.userError "fresh fixture has no compact array layout")
  let json ← must (Json.parse compactText)
  match decodeJson (json.setObjVal! "schema_version" (toJson (8 : Nat))).compress with
  | .error error =>
    unless (error.splitOn "compact array field offsets require schema 9").length > 1 do
      throw (IO.userError s!"wrong legacy-version rejection: {error}")
  | .ok _ => throw (IO.userError "schema 8 accepted new array encoding")
  IO.println "PASS unchanged schema-8 input and schema-9 compact input; schema-8 compact rejection"
