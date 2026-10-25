import Miri.Input.CallResolution

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def candidate (raw : Json) : Bool :=
  ["arguments", "return", "calling_convention", "can_unwind", "c_variadic", "fixed_count"].all
    (fun key => (raw.getObjVal? key).isOk)

def main (args : List String) : IO Unit := do
  let path ← match args with
    | path :: _ => pure path
    | _ => throw (IO.userError "expected current exporter fixture")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let cache := CallResolution.prepareFunctionAbiCache runtime
  let mut count := 0
  for raw in runtime.source.sharedNodes do
    if candidate raw then
      let expected := CallResolution.functionAbiJson runtime raw
      unless CallResolution.functionAbiJson runtime raw (some cache) == expected do
        throw (IO.userError "cached raw ABI differs from direct decoding/conversion")
      count := count + 1
  unless count > 0 do throw (IO.userError "fixture did not exercise shared function ABI")
  -- A complete envelope with malformed payload must retain the direct error.
  let malformed := Json.mkObj [
    ("arguments", toJson (#[] : Array Json)), ("return", Json.null),
    ("calling_convention", Json.null), ("can_unwind", toJson false),
    ("c_variadic", toJson false), ("fixed_count", toJson (0 : Nat))]
  let runtime := { runtime with source := {
      runtime.source with sharedNodes := runtime.source.sharedNodes.push malformed } }
  let cache := CallResolution.prepareFunctionAbiCache runtime
  let expected := CallResolution.functionAbiJson runtime malformed
  unless !expected.isOk && CallResolution.functionAbiJson runtime malformed (some cache) == expected do
    throw (IO.userError "shared malformed ABI did not preserve its direct error")
  IO.println s!"SharedFunctionAbiTests: {count} raw ABI nodes and malformed evidence agree"
