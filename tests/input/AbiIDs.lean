import MiriTests.Input.SharedPayloads
import Miri.Input.CallResolution

open Lean Miri Miri.Input

private def must (result : Except ε α) [ToString ε] : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError (toString error))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: AbiIDs <export.json>")
  let source ← IO.FS.readFile path
  -- Independent source-shaped oracle only; production keeps the wire DAG.
  let oracleCatalog ← must (Reader.Catalog.parse (← must (Json.parse source)))
  let resolved ← must (SharedPayloads.resolveGraph (← must oracleCatalog.input))
  let catalog ← must (Reader.Catalog.parse (← must (Json.parse source)))
  let decoded ← must (decodeRuntimeJson source)
  let runtime ← must (RuntimeMetadata.ofDocument decoded.document)
  let cleanSource := {runtime.source with raw := .null, sharedNodes := #[]}
  let clean := {runtime with source := cleanSource}
  let mut successful := 0
  let mut unavailable := 0
  for (entry, id) in decoded.document.abiTables.functions.toList.zipIdx do
    let some entry := entry | continue
    let some raw := resolved.nodes[id]? | throw (IO.userError "ABI source node missing")
    let expected := decodeCompilerFunctionAbi raw >>= CallResolution.functionAbi runtime
    let actual := CallResolution.functionAbiById clean id
    match expected, actual with
    | .ok expected, .ok actual =>
      unless expected == actual do throw (IO.userError s!"ABI {id}: runtime signature changed")
      successful := successful + 1
    | .error _, .error _ => unavailable := unavailable + 1
    | _, _ => throw (IO.userError s!"ABI {id}: success/failure changed")
    if let .ok entry := entry then
      let some node := catalog.nodes[id]? | throw (IO.userError "wire ABI missing")
      let arguments ← must (catalog.field node "arguments" "ABI")
      if let some expected ← must (catalog.sharedId? arguments "arguments") then
        unless expected == entry.arguments do throw (IO.userError "ABI argument-list ID changed")
      let result ← must (catalog.field node "return" "ABI")
      if let some expected ← must (catalog.sharedId? result "return") then
        unless expected == entry.returnValue do throw (IO.userError "ABI return-argument ID changed")
  let cache := CallResolution.prepareFunctionAbiCache clean
  let mut queries := 0
  let groups := #[
    (decoded.document.abiQueries.instances.map (fun rows => rows.map (·.abi)), ["compiler_instance_abis"], ["abi_query"]),
    (decoded.document.abiQueries.shims.map (fun rows => rows.map (·.abi)), ["compiler_shim_abis"], ["query","abi_query"]),
    (decoded.document.abiQueries.namedShims.map (fun rows => rows.map (·.abi)), ["compiler_named_shim_abis"], ["recipe","query","abi_query"]),
    (decoded.document.abiQueries.pointers.map (fun rows => rows.map (·.abi)), ["compiler_function_facts","pointer_abis"], ["abi_query"]),
    (decoded.document.abiQueries.signatures.map (fun rows => rows.map (·.abi)), ["compiler_function_facts","helper_signatures"], ["abi_query"]) ]
  for (rows, table, keys) in groups do
    let rows ← must rows
    let raw ← must ((← must (table.foldlM Json.getObjVal? resolved.root)).getArr?)
    unless raw.size == rows.size do throw (IO.userError "ABI query count changed")
    for (abi,index) in rows.toList.zipIdx do
      let some record := raw[index]? | throw (IO.userError "ABI query oracle absent")
      let expected := do
        let query ← keys.foldlM (fun (value : Json) key => do
          let value ← value.getObjVal? key
          if key != "recipe" then
            unless (← (← value.getObjVal? "status").getStr?) == "supported" do throw "query unavailable"
          pure value) record
        decodeCompilerFunctionAbi (← query.getObjVal? "value") >>= CallResolution.functionAbi runtime
      let actual := abi.bind (fun id => CallResolution.functionAbiId clean id (some cache))
      match expected, actual with
      | .ok expected, .ok actual =>
        unless expected == actual do throw (IO.userError "global ABI query changed")
      | .error _, .error _ => pure ()
      | _, _ => throw (IO.userError "global ABI query success/failure changed")
      queries := queries + 1
  let mut bodies := decoded.document.bodies.toList
  for entry in decoded.document.instances do
    if let some body := entry.body then bodies := body :: bodies
  let mut cores := bodies.map (·.toBodyCore)
  for body in bodies do
    for child in body.promotedBodies do
      if let some core := child.body then cores := core :: cores
  for entry in decoded.document.instances do
    for child in entry.promotedBodies do
      if let some core := child.body then cores := core :: cores
  let mut sites := 0
  for body in cores do
    for block in body.blocks do
      let some id := block.callAbi | continue
      let some rawBlock := jsonAtPath resolved.root s!"{body.sourcePath}.basic_blocks[{block.id}]" |
        throw (IO.userError "ABI source block absent")
      let raw ← must (rawBlock.getObjVal? "terminator" >>= fun terminator =>
        terminator.getObjVal? "kind" >>= fun kind =>
        kind.getObjVal? "resolution" >>= fun resolution => resolution.getObjVal? "fn_abi")
      let expected := decodeCompilerFunctionAbi raw >>= CallResolution.functionAbi runtime
      let actual := CallResolution.functionAbiId clean id (some cache)
      match expected, actual with
      | .ok expected, .ok actual =>
        unless expected == actual do throw (IO.userError "call-site ABI changed")
      | .error _, .error _ => pure ()
      | _, _ => throw (IO.userError "call-site ABI success/failure changed")
      sites := sites + 1
  IO.println s!"ABI consumers: PASS ({queries} global queries; {sites} call sites)"
  unless successful > 0 do throw (IO.userError "fixture has no usable function ABI")
  IO.println s!"ABI IDs: PASS ({successful} signatures; {unavailable} unavailable; raw source removed)"
