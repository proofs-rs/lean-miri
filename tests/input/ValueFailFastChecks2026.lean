import Miri.Input.DecoderValues

open Lean Miri.Input Miri.Input.DecoderValues

private def errorAt (result : Except String α) (expected : String) : IO Unit := do
  match result with
  | .ok _ => throw (IO.userError s!"accepted invalid value at {expected}")
  | .error message =>
    unless message.startsWith expected do
      throw (IO.userError s!"expected {expected}, got {message}")

private def checkError (value : Json) (path : String) (category : Option TypedEnumTag)
    (expected : String) : IO Unit := do
  errorAt (decodeValue value path .any category) expected

def main : IO Unit := do
  -- The first child's semantic error must stop traversal before the later
  -- malformed MIR node can produce its own parse error.
  let invalidPhase := Json.mkObj [("phase", Json.mkObj [("kind", .str "future_phase")])]
  let laterInvalid := Json.mkObj [("kind", .str "BinaryOp")]
  checkError (.arr #[invalidPhase, laterInvalid]) "$root" none "$root[0].phase.kind:"
  -- Repeated content is checked at the current occurrence, including escaped
  -- object keys.
  checkError (Json.mkObj [("a.b", invalidPhase)]) "$root" none "$root.a%2Eb.phase.kind:"
  checkError (Json.mkObj [("kind", .str "yes"), ("performs_retag", .bool false)])
    "$retag" (some .withRetag) "$retag.performs_retag:"
  checkError (Json.mkObj [("kind", .str "point")])
    "$coverage" (some .coverageKind) "$coverage.point_kind:"
  checkError (Json.mkObj [("kind", .str "BinaryOp"), ("operator", .str "future_op")])
    "$operator" none "$operator.operator:"
  -- A phase stage must agree with its enclosing phase.
  let phase := Json.mkObj [("kind", .str "analysis"),
    ("phase", .str "optimized")]
  checkError phase "$phase" (some .mirPhase) "$phase.phase:"
  let valid := Json.mkObj [("kind", .str "runtime"),
    ("phase", .str "optimized")]
  unless (decodeValue valid "$ok" .any (some .mirPhase)).isOk do
    throw (IO.userError "valid phase rejected")
  let coverage := Json.mkObj [("kind", .str "point"), ("point_kind", .str "expr"),
    ("hir_id", Json.mkObj [("owner_def_id", toJson (0 : Nat)), ("local_id", toJson (7 : Nat))])]
  unless (decodeValue coverage "$probe.coverage" .any (some .coverageKind)).isOk do
    throw (IO.userError "numeric definition ID rejected in source coverage point")
  let oldCoverage := Json.mkObj [("kind", .str "point"), ("point_kind", .str "expr"),
    ("hir_id", Json.mkObj [("owner_def_id", .str "0:1"), ("local_id", toJson (7 : Nat))])]
  checkError oldCoverage "$probe.coverage" (some .coverageKind) "$probe.coverage.hir_id:"
  IO.println "ValueFailFastChecks2026: immediate rejection preserves source paths and phase checks"
