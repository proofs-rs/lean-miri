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
  Json.mkObj fields

private def lowerSignature (program : LoweredProgram) :=
  (program.roots, program.instances, program.promoted,
    program.bundle.bodies.map (·.body), program.bundle.spans,
    program.bundle.definitions, program.bundle.typeConstants)

private def evidenceSignature (prepared : CompilerConstantQueries.Prepared) :=
  prepared.evidence.map fun item =>
    (item.site, item.query.fnInstance, item.query.original, item.query.normalized,
      item.query.span, item.query.value)

private def replaceField (value : Json) (key : String) (replacement : Json) : Json :=
  match value with
  | .obj fields => Json.mkObj (fields.toList.map fun (name, old) =>
      (name, if name == key then replacement else old))
  | _ => value

-- Exercise the two supported normalization-body representations on actual MIR.
-- This changes query evidence only; metadata references keep their owning table.
private partial def embedSourceBodies (value : Json) : Json × Nat := Id.run do
  let mut count := 0
  let value ← match value with
    | .arr values => do
      let mut mapped := #[]
      for child in values do
        let (child, n) := embedSourceBodies child
        count := count + n
        mapped := mapped.push child
      pure (.arr mapped)
    | .obj fields => do
      let mut mapped := []
      for (name, child) in fields.toList do
        let (child, n) := embedSourceBodies child
        count := count + n
        mapped := mapped ++ [(name, child)]
      pure (Json.mkObj mapped)
    | other => pure other
  if let .ok context := value.getObjVal? "constant_query_context" then
    if let .ok normalization := context.getObjVal? "normalization" then
      if (normalization.getObjValAs? String "body_ref").toOption == some "source_body" then
        let .obj fields := value | return (value, count)
        let source := Json.mkObj (fields.toList.filter fun (name, _) => name != "constant_query_context")
        let evidence := Json.mkObj [("body", source)]
        return (replaceField value "constant_query_context"
          (replaceField context "normalization" evidence), count + 1)
  return (value, count)

def main (args : List String) : IO Unit := do
  let embedded := normalized [("body", body)]
  let compact := normalized [("body_ref", toJson "source_body")]
  unless (NormalizationBody.resolve embedded body).toOption == some body do
    throw (IO.userError "embedded normalization body did not resolve")
  unless (NormalizationBody.resolve compact body).toOption == some body do
    throw (IO.userError "compact source_body reference did not resolve")
  mustReject "missing successful body evidence" (NormalizationBody.resolve (Json.mkObj [("kind", toJson "normalization_error")]) body)
  mustReject "missing body and reference" (NormalizationBody.resolve (normalized []) body)
  mustReject "both body and reference" (NormalizationBody.resolve (normalized [("body", body), ("body_ref", toJson "source_body")]) body)
  mustReject "unknown reference" (NormalizationBody.resolve (normalized [("body_ref", toJson "other_body")]) body)
  mustReject "nonstring reference" (NormalizationBody.resolve (normalized [("body_ref", toJson (42 : Nat))]) body)
  mustReject "nonobject embedded body" (NormalizationBody.resolve (normalized [("body", toJson (42 : Nat))]) body)
  mustReject "nonobject source body" (NormalizationBody.resolve compact (toJson (42 : Nat)))

  let graphPath ← match args with
    | path :: _ => pure path
    | _ => throw (IO.userError "expected numeric schema-4 export path")
  let graphText ← IO.FS.readFile graphPath
  let graph ← must (Json.parse graphText)
  let resolved ← must (SharedPayloads.resolveGraph graph)
  unless !resolved.nodes.isEmpty do
    throw (IO.userError "fixture did not exercise semantic metadata tables")
  unless resolved.root == graph && resolved.nodeResolutionCount == 0 do
    throw (IO.userError "semantic table boundary expanded or rewrote numeric input")
  let (inline, embeddedCount) := embedSourceBodies resolved.root
  unless embeddedCount > 0 && inline != graph do
    throw (IO.userError "fixture did not exercise compact normalization bodies")
  let graphDecoded ← must (decodeJson graphText)
  let inlineDecoded ← must (decodeJson inline.compress)
  let graphProgram ← must (lowerProgram graphDecoded.document)
  let inlineProgram ← must (lowerProgram inlineDecoded.document)
  unless lowerSignature graphProgram == lowerSignature inlineProgram do
    throw (IO.userError "graph and resolved inline MIR lowering differ")

  let graphPrepared ← must (CompilerConstantQueries.prepare graphProgram)
  let inlinePrepared ← must (CompilerConstantQueries.prepare inlineProgram)
  unless lowerSignature graphPrepared.program == lowerSignature inlinePrepared.program do
    throw (IO.userError "compact and embedded normalization prepared MIR programs differ")
  unless evidenceSignature graphPrepared == evidenceSignature inlinePrepared do
    throw (IO.userError "graph and resolved inline constant-query evidence differs")
  unless !graphPrepared.evidence.isEmpty do
    throw (IO.userError "fixture did not exercise normalized constant-query evidence")
  IO.println s!"compact and embedded normalization bodies lower and prepare equivalently ({embeddedCount} bodies; {graphPrepared.evidence.size} constant-query results)"
