import Miri.Frontend.Foundation
import Miri.Input.CatalogDecoderRuntime

/-! Pure decoding of finite compiler invocation and consumed-artifact evidence.
The hashes are compiler-input identities, not a proof of reference-sysroot
compatibility. This module performs no filesystem or process operations. -/
namespace Miri.Frontend.Foundation
open Lean

/-- Retain exactly the existing fixed-interpreter producer evidence contract.
Missing settings, malformed digests, or revision/target mismatches reject. -/
def producerOfDocument (document : Document) :
    Except String (Input.Producer × Input.Catalog.ProducerSettings) := do
  let source ← document.source.getObjVal? "producer"
  let producer : Input.Producer := {
    miriCommit := ← source.getObjValAs? String "miri_commit"
    rustcCommit := ← source.getObjValAs? String "rustc_commit"
    rustcVersion := ← source.getObjValAs? String "rustc_version"
    targetTriple := ← source.getObjValAs? String "target_triple"
  }
  unless producer.rustcCommit == (← document.source.getObjValAs? String "rustc_commit") do
    throw "foundation producer rustc revision mismatch"
  unless producer.targetTriple == document.target.triple do
    throw "foundation producer target mismatch"
  unless producer.miriCommit == "7fa591d7d4dd9af8154becbc8332f8096f8323b1" && !producer.rustcVersion.isEmpty do
    throw "foundation producer missing revision/version identity"
  let settingsSource ← source.getObjVal? "input_settings"
  let settings ← Input.JsonReader.run Input.CatalogDecoder.producerSettings settingsSource.compress
  return (producer, settings)

end Miri.Frontend.Foundation
