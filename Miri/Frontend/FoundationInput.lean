import Miri.Frontend.FoundationEntrySeed
import Miri.Input.Decoder

/-! Normal-runner dispatch from the document's schema. Both formats enter the
same lowerer, preparation, interpreter and finalizer. -/
namespace Miri.Frontend.Foundation
open Lean

/-- Decoder handoff preserves the single source World and its derived startup
memo. Recreating it from the document would discard derivation provenance. -/
structure RunnerInput where
  document : Input.ImportDocument
  initialWorld : Option Input.SourceCompilerWorld.World

private def inputSchema (text : String) : Except String (Option String) :=
  Input.JsonReader.run (Input.JsonReader.object none fun schema key => do
    if key == "schema" then return some (← Input.JsonReader.string)
    Input.JsonReader.skipValue
    return schema) text

/-- Select the decoder once, before either route walks its semantic material. -/
def decodeRunnerInputProfiled (text : String) (profile : Options) : Except String RunnerInput :=
  if (inputSchema text).toOption == some (some "lean-miri-foundation") then do
    let source ← (Json.parse text >>= decode).mapError fun error => s!"invalid foundation source: {error}"
    let world ← (compilerEntrySeed source).mapError fun error =>
      s!"foundation compiler-entry Unsupported: {error}"
    return ⟨world.canonical,some world⟩
  else do
    let input ← Input.decodeJsonProfiled text profile
    return ⟨input.document,none⟩

end Miri.Frontend.Foundation
