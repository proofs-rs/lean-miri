import Miri.Frontend.FoundationSourceTypes
import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourcePhysical
import Miri.Input.Decoder
/-! With one pinned snapshot exporter manifest `$M`, generate both inputs:
`python3 tools/export-snapshot-mir.py --build-manifest "$M" -- --foundation --output /tmp/result-source.json --root main --root start -- tests/foundation/fixtures/result-downcast.rs --crate-name result_downcast -Zthreads=1 -Cpanic=abort`
`python3 tools/export-snapshot-mir.py --build-manifest "$M" -- --output /tmp/result-oracle.json --root main -- tests/foundation/fixtures/result-downcast.rs --crate-name result_downcast -Zthreads=1 -Cpanic=abort`
Then run this file with `/tmp/result-source.json /tmp/result-oracle.json`. -/
open Lean Miri Miri.Input Miri.Input.SourceTypes

private def checked (value : Except String α) : IO α := match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

def main (paths : List String) : IO Unit := do
  let [sourcePath,oraclePath] := paths | throw (IO.userError "expected source and compiler oracle")
  let sourceJson ← checked (Json.parse (← IO.FS.readFile sourcePath))
  let source ← checked (Frontend.Foundation.SourceTypesParser.material sourceJson)
  let oracle ← checked (Input.decodeJson (← IO.FS.readFile oraclePath))
  let reference := oracle.document
  let some evidence := reference.runtimeTargetDataLayout | throw (IO.userError "oracle target absent")
  let target ← checked ((RuntimeMetadata.importTarget evidence).mapError toString)
  let actual ← checked (SourcePhysical.calculate source target (← checked (instantiate source #[] #[] 1)))
  let actual ← checked ((RuntimeMetadata.layout target actual).mapError toString)
  let some node := reference.types.find? (·.display == "core::result::Result<u64, u64>") |
    throw (IO.userError "oracle Result<u64,u64> type absent")
  let some expected := reference.layouts[node.layoutId]? | throw (IO.userError "oracle layout absent")
  let expected ← checked ((RuntimeMetadata.layout target expected).mapError toString)
  unless actual == expected do throw (IO.userError s!"direct enum differs from rustc: actual={reprStr actual}, expected={reprStr expected}")
  let document ← checked (Frontend.Foundation.decode sourceJson)
  let world ← checked (Frontend.Foundation.compilerEntrySeed document)
  let (world,id) ← checked (SourcePhysical.intern world (← checked (instantiate source #[] #[] 1)))
  let runtime : RuntimeMetadata := ⟨world.canonical,target⟩
  let parent ← checked (runtime.lookup id |>.mapError toString)
  let tag ← checked (runtime.field parent 0 |>.mapError toString)
  let some queries := node.compilerFacts.bind (·.projectionQueries) | throw (IO.userError "oracle projections absent")
  let some defaultParent := queries.parents.find? (·.variant.isNone) | throw (IO.userError "oracle default parent absent")
  let some tagField := defaultParent.fields.find? (·.index == 0) | throw (IO.userError "oracle tag field absent")
  let some tagLayout := reference.layouts[tagField.layoutId]? | throw (IO.userError "oracle tag layout absent")
  let tagLayout ← checked ((RuntimeMetadata.layout target tagLayout).mapError toString)
  unless tag.layout == tagLayout do throw (IO.userError "synthetic enum tag field differs from rustc full layout")
  IO.println "PASS typed direct-tag enum and synthetic tag field full layouts equal pinned rustc"
