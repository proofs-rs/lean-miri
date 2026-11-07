import Miri.Input.Reader.SessionMetadata

open Lean Miri.Input Miri.Input.Reader

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def catalog (rows : String) : IO Catalog := do
  must (Catalog.parse (← must (Json.parse rows)))

def main : IO Unit := do
  let source ← catalog "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[\"sse2\",[ {\"$lean_miri_shared_ref\":0} ],{\"internal_target_features\":{\"$lean_miri_shared_ref\":1}},{\"crate\":7,\"name\":\"example\"},[{\"$lean_miri_shared_ref\":3}],{\"local_crate\":7,\"crates\":{\"$lean_miri_shared_ref\":4}}]},\"compiler_session_queries\":{\"$lean_miri_shared_ref\":2},\"compiler_frame_metadata\":{\"$lean_miri_shared_ref\":5}}"
  let session ← must (SessionMetadataReader.session source)
  unless (← must session.internalTargetFeatures) == #["sse2"] do
    throw (IO.userError "shared target features changed")
  unless session.isLikeWasm.toOption.isNone do
    throw (IO.userError "missing wasm query must remain unavailable independently")
  let frame ← must (SessionMetadataReader.frame source)
  unless frame.localCrate == 7 && frame.crates == #[(7,"example")] do
    throw (IO.userError "shared frame metadata changed")
  let duplicate ← catalog "{\"shared_payloads\":{\"schema_version\":2,\"nodes\":[]},\"compiler_frame_metadata\":{\"local_crate\":7,\"crates\":[{\"crate\":7,\"name\":\"a\"},{\"crate\":7,\"name\":\"b\"}]}}"
  unless (SessionMetadataReader.frame duplicate).toOption.isNone do
    throw (IO.userError "duplicate crate identity accepted")
