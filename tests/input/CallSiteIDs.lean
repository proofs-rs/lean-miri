import MiriTests.Input.SharedPayloads
import Miri.Input.CallResolution

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def same [BEq α] (actual expected : Except String α) : Bool :=
  match actual, expected with
  | .ok a, .ok b => a == b
  | .error _, .error _ => true
  | _, _ => false

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: CallSiteIDs <export.json>")
  let source ← IO.FS.readFile path
  let decoded ← must (decodeRuntimeJson source)
  let program ← must (lowerCoreProgram decoded.document)
  -- This legacy source-shaped view is an independent QA oracle.
  let catalog ← must (Reader.Catalog.parse (← must (Json.parse source)))
  let resolved ← must (SharedPayloads.resolveCatalog (← must catalog.input))
  let mut calls := 0
  for (body,index) in program.bundle.bodies.toList.zipIdx do
    let some metadata := decoded.document.mirTables.bodySources[index]? |
      throw (IO.userError "typed body metadata absent")
    let some source := jsonAtPath resolved body.input.sourcePath |
      throw (IO.userError s!"oracle body absent: {body.input.sourcePath}")
    let blocks ← must ((← must (source.getObjVal? "basic_blocks")).getArr?)
    unless metadata.calls.size == blocks.size do throw (IO.userError "call-site block order changed")
    for (raw,index) in blocks.toList.zipIdx do
      let kind ← must (raw.getObjVal? "terminator" >>= fun term => term.getObjVal? "kind")
      let variant ← must (kind.getObjValAs? String "variant")
      let some row := metadata.calls[index]? | throw (IO.userError "typed call-site row absent")
      if variant != "Call" && variant != "TailCall" then
        unless row == .ok none do throw (IO.userError "non-call block acquired resolution metadata")
        continue
      let expected ← must (kind.getObjVal? "resolution")
      let some actual ← must row | throw (IO.userError "call-site metadata absent")
      unless same actual.status (expected.getObjValAs? String "status") &&
          same actual.kind (expected.getObjValAs? String "kind") &&
          same actual.instanceId (expected.getObjValAs? Nat "instance_id") &&
          same actual.dispatchSlot (expected.getObjValAs? Nat "dispatch_slot") &&
          same actual.functionType (expected.getObjVal? "function_type" >>= fun ty => ty.getObjValAs? Nat "type_id") do
        throw (IO.userError "call-site typed field semantics changed")
      calls := calls + 1
  unless calls > 0 do throw (IO.userError "fixture contains no calls")
  IO.println s!"call-site IDs: PASS ({calls} call/tail-call sites)"
