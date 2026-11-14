import Miri.Input.Decoder
import Miri.Input.CallResolution
open Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error reason => throw (IO.userError reason)
def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh candidate export")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let mut seeded := 0
  let mut negative := 0
  for id in [:runtime.source.functionAbis.size] do
    let some source := runtime.source.functionAbis[id]? | throw (IO.userError "ABI table index invariant")
    let result ← must (CallResolution.functionAbiId runtime id)
    if let some material := source.signatureSeed then
      seeded := seeded + 1
      unless result.fixedCount.toNat == material.signature.inputs.size -
          (if material.signature.abi == .RustCall then 1 else 0) do
        throw (IO.userError "source fixed-count construction failed")
      -- Force an extra argument on a nonvariadic signature. It must fail at
      -- source argument planning, regardless of otherwise valid physical rows.
      if !material.signature.cVariadic && material.signature.abi != .RustCall then
        let malformed := { source with signatureSeed := some {
          material with extraArgumentTypes := #[material.signature.output] } }
        match CallResolution.functionAbi runtime malformed with
        | .error _ => negative := negative + 1
        | .ok _ => throw (IO.userError "nonvariadic construction accepted extra argument")
  unless seeded > 0 && negative > 0 do
    throw (IO.userError "fresh export exercised no source signature construction controls")
  IO.println s!"Runtime signature reconstruction: {seeded} seeded rows, {runtime.source.functionAbis.size - seeded} residual rows, {negative} malformed extras rejected."
