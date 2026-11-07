import MiriTests.Input.SharedPayloads
import Miri.Input.Decoder

open Lean Miri Miri.Input

private def must (value : Except String A) : IO A :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def replace (input : Json) (key : String) (value : Json) : Except String Json := do
  let .obj fields := input | throw "expected object"
  return Json.mkObj ((key,value) :: fields.toList.filter (fun entry => entry.1 != key))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: VtableEntryIDs <export.json>")
  let source ← IO.FS.readFile path
  -- Independent source-shaped oracle only; production keeps the wire DAG.
  let resolved ← must (SharedPayloads.resolveGraph (← must (Json.parse source)))
  let root ← must (Json.parse source)
  let decoded ← must (decodeRuntimeJson source)
  let document := decoded.document
  let mut entries := 0
  let mut methods := 0
  for (slot,id) in document.vtableTables.entryLists.toList.zipIdx do
    let some actual := slot | continue
    let some raw := resolved.nodes[id]? | throw (IO.userError "vtable list source absent")
    let values ← must raw.getArr?
    unless actual.size == values.size do throw (IO.userError "vtable entry count changed")
    for (value,index) in values.toList.zipIdx do
      let expected ← must (decodeVtableEntry value)
      let some actual := actual[index]? | throw (IO.userError "vtable entry absent")
      unless actual.kind == expected.kind && actual.status == expected.status &&
          actual.instanceId == expected.instanceId && actual.allocationId == expected.allocationId do
        throw (IO.userError "vtable entry semantics changed")
      entries := entries + 1
      if actual.kind == .method then methods := methods + 1
  unless methods > 0 do throw (IO.userError "fixture has no vtable methods")
  let shared ← must (root.getObjVal? "shared_payloads")
  let nodes ← must (shared.getObjVal? "nodes" >>= Json.getArr?)
  let some index := nodes.findIdx? (fun node => node.getObjValAs? String "kind" == .ok "method") |
    throw (IO.userError "wire method node absent")
  let some node := nodes[index]? | throw (IO.userError "wire method missing")
  for (key,value) in [("instance_id",toJson document.instances.size),
      ("def_id",Json.mkObj [("crate",toJson (999999 : Nat)),("index",toJson (999999 : Nat))])] do
    let mutated ← must (replace node key value)
    let nodes ← if bound : index < nodes.size then pure (nodes.set index mutated bound)
      else throw (IO.userError "wire method index invalid")
    let shared ← must (replace shared "nodes" (.arr nodes))
    let root ← must (replace root "shared_payloads" shared)
    unless !(decodeRuntimeJson root.compress).isOk do
      throw (IO.userError s!"inconsistent vtable method {key} accepted")
  IO.println s!"vtable entry IDs: PASS ({entries} entries; {methods} methods; invalid instance/definition rejected)"
