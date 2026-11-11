import Miri.Input.Decoder

open Lean Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [legacyPath, compactPath] := args | throw (IO.userError "expected current dense-offset and compact-offset pooled inputs")
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
  let references ← must (json.getObjValAs? (Array Nat) "layouts")
  let payloads ← must (json.getObjValAs? (Array Json) "layout_values")
  unless references.size == compact.document.layouts.size && references.all (· < payloads.size) do
    throw (IO.userError "compact layout payload pool changed LayoutId identities")
  for version in #[8, 9] do
    match decodeJson (json.setObjVal! "schema_version" (toJson version)).compress with
    | .error error =>
      unless (error.splitOn "unsupported schema version").length > 1 do
        throw (IO.userError s!"wrong obsolete-version rejection: {error}")
    | .ok _ => throw (IO.userError s!"obsolete schema {version} accepted current array encoding")
  IO.println "PASS current dense and compact pooled inputs; schemas 8 and 9 rejected"
