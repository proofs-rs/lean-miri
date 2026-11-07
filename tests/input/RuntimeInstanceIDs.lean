import Miri.Input.Decoder
import Miri.Input.CompilerInstance
import Miri.Input.Reader.RuntimeInstances

open Lean Miri Miri.Input

private def must (value : Except String A) : IO A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def replace (input : Json) (key : String) (value : Json) : Except String Json := do
  let .obj fields := input | throw "expected object"
  return Json.mkObj ((key,value) :: fields.toList.filter (fun entry => entry.1 != key))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: RuntimeInstanceIDs <export.json>")
  let source ← IO.FS.readFile path
  let decoded ← must (decodeRuntimeJson source)
  let document := decoded.document
  let tables := document.mirTables
  let records ← must tables.runtimeInstances
  let raw ← must (document.raw.getObjVal? "compiler_runtime_queries" >>= fun value =>
    value.getObjVal? "instances" >>= Json.getArr?)
  unless records.size == raw.size do throw (IO.userError "runtime instance metadata count changed")
  let ctx := LowerContext.ofDocument document
  for (record,index) in records.toList.zipIdx do
    let some input := raw[index]? | throw (IO.userError "runtime instance source absent")
    let (expected,next) ← must (CompilerInstance.decode ctx tables.compiler input)
    let actual ← must (tables.instance record.instanceId)
    unless expected == actual do
      throw (IO.userError "runtime metadata refers to another complete instance")
    unless next = tables.compiler do
      throw (IO.userError "runtime metadata introduces another compiler identity")
    unless record.display == (← must (input.getObjValAs? String "display")) &&
        record.inlineNever == (← must (input.getObjValAs? Bool "inline_never")) &&
        record.callerLocation == (← must (input.getObjValAs? Bool "requires_caller_location")) do
      throw (IO.userError "runtime instance metadata changed")
    let expectedName := do
      let query ← input.getObjVal? "item_name"
      unless (← query.getObjValAs? String "status") == "supported" do throw "unavailable"
      query.getObjValAs? String "value"
    match expectedName,record.itemName with
    | .ok expected,.ok actual => unless expected == actual do throw (IO.userError "item name changed")
    | .error _,.error _ => pure ()
    | _,_ => throw (IO.userError "item name availability changed")
  let root ← must (Json.parse source)
  let catalog ← must (Reader.Catalog.parse root)
  let some index := catalog.nodes.findIdx? (fun node =>
      (node.getObjVal? "requires_caller_location").isOk) |
    throw (IO.userError "runtime metadata wire node absent")
  let some node := catalog.nodes[index]? | throw (IO.userError "runtime metadata node absent")
  let changed ← must (replace node "instance_id" (toJson tables.instances.size))
  let nodes ← if bound : index < catalog.nodes.size then pure (catalog.nodes.set index changed bound)
    else throw (IO.userError "runtime metadata node index invalid")
  let shared ← must (replace (← must (root.getObjVal? "shared_payloads")) "nodes" (.arr nodes))
  let root ← must (replace root "shared_payloads" shared)
  let mutated ← must (Reader.Catalog.parse root)
  unless !(mutated.readRuntimeInstances tables.instances.size).isOk do
    throw (IO.userError "out-of-bounds runtime instance ID accepted")
  IO.println s!"runtime instance IDs: PASS ({records.size} records; metadata and complete identity; invalid ID rejected)"
