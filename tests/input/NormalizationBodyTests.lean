import Miri.Input.CompilerConstantQueries
import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Lean Miri.Input Miri.MIR

private def must (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def mustReject (name : String) (value : Except String α) : IO Unit :=
  match value with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"normalization resolver accepted malformed case: {name}")

private def body : Json := Json.mkObj [("basic_blocks", toJson (#[] : Array Json))]

private def normalized (fields : List (String × Json)) : Json :=
  Json.mkObj (("status", toJson "supported") :: fields)

private def lowerSignature (program : LoweredProgram) :=
  (program.roots, program.instances, program.promoted,
    program.bundle.bodies.map (·.body), program.bundle.spans,
    program.bundle.definitions, program.bundle.typeConstants)

private def evidenceSignature (prepared : CompilerConstantQueries.Prepared) :=
  prepared.evidence.map fun item =>
    (item.site, item.query.fnInstance, item.query.original, item.query.normalized,
      item.query.span, item.query.value)

def main (args : List String) : IO Unit := do
  let legacy := normalized [("body", body)]
  let compact := normalized [("body_ref", toJson "source_body")]
  unless (NormalizationBody.resolve legacy body).toOption == some body do
    throw (IO.userError "legacy embedded normalization body did not resolve")
  unless (NormalizationBody.resolve compact body).toOption == some body do
    throw (IO.userError "compact source_body reference did not resolve")
  mustReject "unsupported status" (NormalizationBody.resolve (Json.mkObj [("status", toJson "unsupported"), ("body", body)]) body)
  mustReject "missing body and reference" (NormalizationBody.resolve (normalized []) body)
  mustReject "both body and reference" (NormalizationBody.resolve (normalized [("body", body), ("body_ref", toJson "source_body")]) body)
  mustReject "unknown reference" (NormalizationBody.resolve (normalized [("body_ref", toJson "other_body")]) body)
  mustReject "nonstring reference" (NormalizationBody.resolve (normalized [("body_ref", toJson (42 : Nat))]) body)
  mustReject "nonobject embedded body" (NormalizationBody.resolve (normalized [("body", toJson (42 : Nat))]) body)
  mustReject "nonobject source body" (NormalizationBody.resolve compact (toJson (42 : Nat)))

  let graphPath ← match args with
    | path :: _ => pure path
    | _ => throw (IO.userError "expected shared-graph export path")
  let graphText ← IO.FS.readFile graphPath
  let graph ← must (Json.parse graphText)
  let resolved ← must (SharedPayloads.resolveGraph graph)
  unless !resolved.nodes.isEmpty do
    throw (IO.userError "fixture did not exercise shared payload nodes")
  let inline ← match resolved.root with
    | .obj fields => pure (Json.mkObj (("shared_payloads", Json.mkObj [
        ("schema_version", toJson (2 : Nat)), ("nodes", toJson (#[] : Array Json))]) :: fields.toList))
    | _ => throw (IO.userError "resolved fixture is not an object")
  let graphDecoded ← must (decodeJson graphText)
  let inlineDecoded ← must (decodeJson inline.compress)
  let graphProgram ← must (lowerProgram graphDecoded.document)
  let inlineProgram ← must (lowerProgram inlineDecoded.document)
  unless lowerSignature graphProgram == lowerSignature inlineProgram do
    throw (IO.userError "graph and resolved inline MIR lowering differ")
  unless graphProgram.input.obligations == inlineProgram.input.obligations do
    throw (IO.userError "graph and resolved inline source obligations differ")

  let graphPrepared ← must (CompilerConstantQueries.prepare graphProgram)
  let inlinePrepared ← must (CompilerConstantQueries.prepare inlineProgram)
  unless lowerSignature graphPrepared.program == lowerSignature inlinePrepared.program do
    throw (IO.userError "graph and resolved inline prepared MIR programs differ")
  unless evidenceSignature graphPrepared == evidenceSignature inlinePrepared do
    throw (IO.userError "graph and resolved inline constant-query evidence differs")
  unless graphPrepared.obligations == inlinePrepared.obligations do
    throw (IO.userError "graph and resolved inline preparation obligations differ")
  unless !graphPrepared.evidence.isEmpty do
    throw (IO.userError "fixture did not exercise normalized constant-query evidence")
  IO.println s!"graph and resolved inline inputs decode, lower, and prepare equivalently ({graphProgram.bundle.bodies.size} bodies; {graphPrepared.evidence.size} constant-query results)"
