import Miri.Input.Decoder
import MiriTests.Connected.Proofs.JsonDecidableEq213

/-! Exact field comparisons, not just JSON payload comparisons. The transport
adapter is implemented in Rust; canonical decoding is the independent oracle. -/
open Lean Miri.Input

deriving instance DecidableEq for TaggedNode
deriving instance DecidableEq for FieldShape
deriving instance DecidableEq for PrimitiveLayout
deriving instance DecidableEq for ScalarLayout
deriving instance DecidableEq for BackendRepr
deriving instance DecidableEq for LayoutVariant
deriving instance DecidableEq for TagEncoding
deriving instance DecidableEq for VariantsLayout
deriving instance DecidableEq for Layout
deriving instance DecidableEq for CanonicalAbi
deriving instance DecidableEq for AbiAttributes
deriving instance DecidableEq for AbiRegister
deriving instance DecidableEq for AbiCastTarget
deriving instance DecidableEq for AbiPassMode
deriving instance DecidableEq for AbiArgument
deriving instance DecidableEq for FunctionAbi

private def must {α : Type} : Except String α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def reference (id : Nat) : Json :=
  Json.mkObj [("$lean_miri_shared_ref", toJson id)]

private def graph (nodes : Array Json) (version : Json := toJson (1 : Nat)) : Json :=
  Json.mkObj [("root", reference (nodes.size - 1)), ("shared_payloads", Json.mkObj [
    ("schema_version", toJson (2 : Nat)), ("typed_abi_version", version), ("nodes", .arr nodes)])]

private def checkTransport : IO Unit := do
  let arg := Json.mkObj [(AbiWire.argumentMarker, .arr #[toJson (7 : Nat), .null, .null])]
  let fn := Json.mkObj [(AbiWire.functionMarker, .arr #[toJson (1 : Nat), toJson (0 : Nat),
    .null, .bool false, .bool false, toJson (1 : Nat)])]
  let nodes := #[arg, .arr #[reference 0], fn]
  let (resolved, cached) ← must (JsonTraversalCache.resolve (graph nodes))
  unless cached.audit && resolved.typedAbi.arguments.size == 1 && resolved.typedAbi.functions.size == 1 do
    throw (IO.userError "typed graph did not retain canonical values/hash identities")
  let withFlags := match graph nodes with
    | .obj fields => .obj (fields.insert "shared_payloads" (Json.mkObj [
        ("schema_version", toJson (2 : Nat)), ("typed_abi_version", toJson (1 : Nat)),
        ("nodes", .arr nodes), ("scan_flags", toJson (#[1, 1, 5] : Array Nat))]))
    | other => other
  let (_, flagged) ← must (JsonTraversalCache.resolve withFlags)
  unless flagged.audit do throw (IO.userError "typed ABI plus scan-summary validation differs")
  let malformed := #[
    graph nodes (toJson (2 : Nat)),
    graph #[Json.mkObj [(AbiWire.argumentMarker, .arr #[.bool true, .null, .null])]],
    graph #[Json.mkObj [(AbiWire.argumentMarker, .arr #[toJson (0 : Nat)])]],
    graph #[arg, fn], -- vector is not earlier
    graph #[.arr #[], fn], -- return is not an argument
    graph #[arg, .arr #[reference 0], Json.mkObj [(AbiWire.functionMarker,
      .arr #[toJson (1 : Nat), toJson (0 : Nat), .null, toJson (0 : Nat), .bool false, toJson (1 : Nat)])]],
    graph #[Json.mkObj [("nested", arg)]]]
  for value in malformed do
    match SharedPayloads.resolveGraph value with
    | .error _ => pure ()
    | .ok _ => throw (IO.userError "malformed typed ABI transport accepted")

def main (args : List String) : IO Unit := do
  checkTransport
  let path :: rest := args | throw (IO.userError "expected packed ABI snapshot")
  unless rest == [] || rest == ["--full"] do throw (IO.userError "unexpected test option")
  let text ← IO.FS.readFile path
  let raw ← must (Json.parse text)
  let resolved ← must (SharedPayloads.resolveGraph raw)
  unless !resolved.typedAbi.functions.isEmpty do throw (IO.userError "fixture has no typed ABI records")
  let ordinary := DecoderValues.sharedDecodeMemo resolved.nodes
  let direct := DecoderValues.prepareTypedAbiMemo resolved.typedAbi ordinary
  let mut count := 0
  for node in resolved.nodes do
    if DecoderValues.isFunctionAbiCandidate node then
      let canonical := DecoderValues.parseFunctionAbi node "$probe" ordinary
      let prepared := DecoderValues.parseFunctionAbi node "$probe" direct
      match canonical, prepared with
      | .ok a, .ok b => unless decide (a = b) do
          throw (IO.userError "typed ABI differs in a decoded field")
      | .error a, .error b => unless a == b do throw (IO.userError "ABI error changed")
      | _, _ => throw (IO.userError "ABI success/failure changed")
      count := count + 1
  IO.println s!"typed ABI transport and all decoded ABI fields: PASS ({count} records)"
  if rest == ["--full"] then
    match decodeRuntimeJson text, decodeRuntimeJsonReference text with
    | .ok a, .ok b =>
      unless a.executionInput.isSome == b.executionInput.isSome &&
          a.blockingObligations == b.blockingObligations &&
          a.document.obligations == b.document.obligations &&
          decide (a.document.functionAbis = b.document.functionAbis) &&
          a.document.raw == b.document.raw do
        throw (IO.userError "typed decoder readiness, obligations or ABI fields changed")
    | .error a, .error b => unless a == b do throw (IO.userError "first decoder error changed")
    | _, _ => throw (IO.userError "decoder result class changed")
    IO.println "typed/canonical full decoder ordered obligations and all ABI fields: PASS"
