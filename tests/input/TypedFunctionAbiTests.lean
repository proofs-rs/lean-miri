import MiriTests.Input.JsonFixtures
import Miri.Input.CallResolution

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def rejects (value : Except String α) (message : String) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError message)

private def set (value : JsonFixtures.Value) (key child : String) : Except String JsonFixtures.Value := do
  let fields ← value.object
  let entries := fields.map fun (name, old) =>
    "\"" ++ name ++ "\":" ++ (if name == key then child else old.text)
  JsonFixtures.parse ("{" ++ String.intercalate "," entries.toList ++ "}")

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected exporter MIR input")
  let text ← IO.FS.readFile path
  let decoded ← must (decodeJson text)
  let source ← must (JsonFixtures.parse text)
  let rawAbis ← must ((← must (source.field "fn_abis")).array)
  let rawArguments ← must ((← must (source.field "abi_arguments")).array)
  let argumentPool ← rawArguments.mapM fun value => must (JsonReader.run (DecoderValues.parseAbiArgument "$.abi_arguments") value.text)
  let parseAbi := DecoderValues.parseFunctionAbi "$.fn_abis" (some argumentPool)
  let layoutIds ← must ((← must (source.field "layouts")).array)
  let rawLayouts ← must ((← must (source.field "layout_values")).array)
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  check (!runtime.source.functionAbis.isEmpty) "fixture contains no function ABI definitions"
  for (abi, id) in runtime.source.functionAbis.toList.zipIdx do
    let some rawAbi := rawAbis[id]? | throw (IO.userError "missing input ABI row")
    let parsed ← must (JsonReader.run parseAbi rawAbi.text)
    check (CallResolution.functionAbi runtime parsed == CallResolution.functionAbi runtime abi)
      "typed ABI table differs from its definition"
    check (CallResolution.functionAbiId runtime id == CallResolution.functionAbi runtime abi)
      "numeric ABI lookup differs from typed conversion"
  rejects (CallResolution.functionAbiId runtime runtime.source.functionAbis.size)
    "out of bounds ABI accepted"
  let wrappedId ← must (JsonFixtures.parse "{\"fn_abi_id\":0}")
  rejects wrappedId.natural "object ABI reference accepted"
  let some sample := runtime.source.functionAbis[0]? | throw (IO.userError "missing first function ABI")
  let invalidArity := { sample with fixedCount := sample.arguments.size + 1 }
  let arityRuntime := { runtime with source := { runtime.source with functionAbis := #[invalidArity] } }
  match CallResolution.functionAbiId arityRuntime 0 with
  | .error message => check (message.contains "fixed_count exceeds actual arguments") "arity diagnostic changed"
  | .ok _ => throw (IO.userError "ABI arity check bypassed")
  let invalidConvention := { sample with callingConvention :=
    { sample.callingConvention with kind := .arm, armCall := none } }
  let conventionRuntime := { runtime with source := { runtime.source with functionAbis := #[invalidConvention] } }
  rejects (CallResolution.functionAbiId conventionRuntime 0) "missing calling convention evidence accepted"
  let layoutId := sample.returnValue.layoutId
  let some layout := runtime.source.layouts[layoutId]? | throw (IO.userError "fixture return layout missing")
  let oversized := { layout with sizeBytes := some (2^64) }
  let sizeRuntime := { runtime with source := { runtime.source with
    functionAbis := #[sample], layouts := runtime.source.layouts.set! layoutId oversized } }
  match CallResolution.functionAbiId sizeRuntime 0 with
  | .error message => check (message.contains "u64 overflow") "physical size overflow diagnostic changed"
  | .ok _ => throw (IO.userError "ABI layout-size check bypassed")
  let invalidLayout := { sample.returnValue with layoutId := runtime.source.layouts.size }
  let layoutRuntime := { runtime with source := { runtime.source with
    functionAbis := #[{ sample with returnValue := invalidLayout }] } }
  rejects (CallResolution.functionAbiId layoutRuntime 0) "out of bounds physical layout accepted"
  let some rawId := layoutIds[layoutId]? | throw (IO.userError "missing raw layout reference")
  let payloadId ← must rawId.natural
  let some rawLayout := rawLayouts[payloadId]? | throw (IO.userError "missing raw return layout")
  let malformedLayout ← must (set rawLayout "field_offsets_bytes" "\"not-an-array\"")
  rejects (JsonReader.run DecoderValues.decodeCompilerLayout malformedLayout.text) "malformed layout definition accepted"
  let some rawSample := rawAbis[0]? | throw (IO.userError "missing raw ABI sample")
  let missingArgument ← must (set rawSample "return" (toString argumentPool.size))
  rejects (JsonReader.run parseAbi missingArgument.text) "out of bounds shared ABI argument accepted"
  let returnId ← must ((← must (rawSample.field "return")).natural)
  let some returnValue := rawArguments[returnId]? | throw (IO.userError "missing return argument")
  let inlineArgument ← must (set rawSample "return" returnValue.text)
  rejects (JsonReader.run parseAbi inlineArgument.text) "inline ABI argument accepted at pooled ID position"
  let inlineReturn ← must (set returnValue "layout" rawLayout.text)
  let inlineAbi ← must (set rawSample "return" inlineReturn.text)
  rejects (JsonReader.run parseAbi inlineAbi.text) "inline physical layout accepted at ID position"
  IO.println s!"typed ABI table: {runtime.source.functionAbis.size} definitions; bounds, arity, convention and physical layout checks passed"
