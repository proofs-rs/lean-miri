import Miri.Frontend.FoundationProducer

open Lean Miri.Frontend.Foundation

private def checkError (document : Document) : IO Unit := do
  match producerOfDocument document with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "malformed producer evidence accepted")

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh foundation JSON path")
  let contents ← IO.FS.readFile path
  let document ← match Json.parse contents >>= decode with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let (producer, settings) ← match producerOfDocument document with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  unless producer.targetTriple == document.target.triple && settings.hashAlgorithm == "sha256" do
    throw (IO.userError "producer source identity mismatch")
  let source ← match document.source.getObjVal? "producer" with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let rawSettings ← match source.getObjVal? "input_settings" with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  for changed in #[source.setObjVal! "rustc_commit" (toJson "wrong"),
      source.setObjVal! "miri_commit" (toJson "wrong"),
      source.setObjVal! "target_triple" (toJson "wrong"),
      source.setObjVal! "input_settings" Json.null,
      source.setObjVal! "input_settings" (rawSettings.setObjVal! "sysroot_manifest_sha256" (toJson "wrong"))] do
    checkError { document with source := document.source.setObjVal! "producer" changed }
  IO.println "foundation producer: fresh evidence and five malformed controls passed"
