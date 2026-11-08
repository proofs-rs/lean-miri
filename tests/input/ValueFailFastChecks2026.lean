import Miri.Input.DecoderValues

open Lean Miri.Input Miri.Input.DecoderValues

private def errorAt (result : Except String α) (expected : String) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"accepted invalid value at {expected}")
  | .error message =>
    unless message.startsWith expected do
      throw (IO.userError s!"expected {expected}, got {message}")

private def checkBoth (value : Json) (path : String) (category : Option TypedEnumTag)
    (expected : String) : IO Unit := do
  errorAt (decodeValue value path .any category) expected
  errorAt (decodeRuntimeValue (.uncached value) path .any category) expected

def main : IO Unit := do
  -- The first child's semantic error must stop traversal before the later
  -- malformed MIR node can produce its own parse error.
  let invalidPhase := Json.mkObj [("phase", Json.mkObj [("kind", .str "future_phase")])]
  let laterInvalid := Json.mkObj [("kind", .str "BinaryOp")]
  checkBoth (.arr #[invalidPhase, laterInvalid]) "$root" none "$root[0].phase.kind:"
  -- Repeated content is checked at the current occurrence, including escaped
  -- object keys. Failed decodes cannot install a path-bearing cache entry.
  checkBoth (Json.mkObj [("a.b", invalidPhase)]) "$root" none "$root.a%2Eb.phase.kind:"
  checkBoth (Json.mkObj [("kind", .str "yes"), ("performs_retag", .bool false)])
    "$retag" (some .withRetag) "$retag.performs_retag:"
  checkBoth (Json.mkObj [("kind", .str "point")])
    "$coverage" (some .coverageKind) "$coverage.point_kind:"
  checkBoth (Json.mkObj [("kind", .str "BinaryOp"), ("operator", .str "future_op")])
    "$operator" none "$operator.operator:"
  -- Parent checks still consume the small runtime child summaries.
  let phase := Json.mkObj [("kind", .str "analysis"),
    ("phase", .str "optimized")]
  checkBoth phase "$phase" (some .mirPhase) "$phase.phase:"
  let valid := Json.mkObj [("kind", .str "runtime"),
    ("phase", .str "optimized")]
  unless (decodeValue valid "$ok" .any (some .mirPhase)).isOk &&
      (decodeRuntimeValue (.uncached valid) "$ok" .any (some .mirPhase)).isOk do
    throw (IO.userError "valid phase rejected")
  IO.println "ValueFailFastChecks2026: immediate rejection and full/runtime diagnostics agree"
