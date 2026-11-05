import Miri.Input.Decoder

open Lean Miri.Input Miri.Input.DecoderValues

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def set (j : Json) (key : String) (value : Json) : Json :=
  match j with
  | .obj fields => Json.mkObj ((key,value) :: fields.toList.filter (·.1 != key))
  | _ => Json.mkObj [(key,value)]

-- Convert independently from complete legacy facts; this must reproduce the
-- entire typed world, not merely a terminal result from one guest execution.
private def compact (world : Json) : Except String Json := do
  let rows ← arrayField world "raw_pool" "$world"
  let mut kinds := ""
  let mut opaqueRows := #[]
  for row in rows do
    let kind ← fieldString row "kind" "$row"
    kinds := kinds ++ (← match kind with
      | "dangling" => pure "d" | "memory" => pure "m" | "function" => pure "f"
      | "vtable" => pure "v" | "static" => pure "s" | "type_id" => pure "t"
      | _ => throw "unknown legacy kind")
    if kind == "memory" && (← fieldString row "status" "$row") == "opaque" then
      opaqueRows := opaqueRows.push row
  let fields ← world.getObj?
  pure (Json.mkObj ([("schema", .str "rustc_alloc_id_world_v2"),
    ("raw_kinds", .str kinds), ("opaque_memory", .arr opaqueRows)] ++
    fields.toList.filter (fun (key,_) => key != "schema" && key != "raw_pool")))

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected a genuine legacy-world compiler export")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let nodes := decoded.document.allocations
  let raw := decoded.document.raw
  let world ← must (raw.getObjVal? "compiler_alloc_id_world")
  check ((← must (fieldString world "schema" "$world")) == "rustc_alloc_id_world_v1")
    "comparison source must be legacy facts"
  let expected ← must (parseCompilerAllocIdWorld world nodes)
  let normalized ← must (compact world)
  let actual ← must (parseCompilerAllocIdWorld normalized nodes)
  check (actual == expected) "normalization changed complete pool/catalog facts"
  let newRaw := set raw "compiler_alloc_id_world" normalized
  let _ ← must (validateCompilerAllocIdWorldRaw newRaw nodes (some actual))
  let reject := fun (j : Json) (label : String) =>
    check (!(parseCompilerAllocIdWorld j nodes).isOk) s!"accepted malformed compact world: {label}"
  let kinds ← must (fieldString normalized "raw_kinds" "$world")
  for bad in ["", kinds ++ "d", "?" ++ (kinds.drop 1).toString,
      (kinds.dropEnd 1).toString ++ "f"] do
    reject (set normalized "raw_kinds" (.str bad)) "prefix/kind/sentinel"
  reject (set normalized "raw_pool" (.arr #[])) "mixed encodings"
  reject (set normalized "schema" (.str "rustc_alloc_id_world_v3")) "unknown schema"
  let opaqueRows ← must (arrayField normalized "opaque_memory" "$world")
  let bogus := Json.mkObj [("source_alloc_id", toJson (kinds.length + 1)),
    ("kind", .str "memory"), ("status", .str "opaque"), ("allocation_id", .null),
    ("memory_mutability", .str "mutable"), ("memory_align_bytes", toJson (8 : Nat)),
    ("memory_all_bytes_initialized", .bool true), ("memory_has_provenance", .bool false)]
  reject (set normalized "opaque_memory" (.arr (opaqueRows.push bogus))) "out-of-prefix projection"
  if let some row := opaqueRows[0]? then
    reject (set normalized "opaque_memory" (.arr (opaqueRows.push row))) "duplicate projection"
    reject (set normalized "opaque_memory" (.arr (opaqueRows.extract 1 opaqueRows.size))) "missing projection"
  if let some node := nodes[0]? then
    let broken := nodes.set! 0 {node with sourceAllocId := some (UInt64.ofNat (kinds.length + 1))}
    check (!(parseCompilerAllocIdWorld normalized broken).isOk) "accepted foreign source witness"
    check (!(validateCompilerAllocIdWorldRaw newRaw broken (some actual)).isOk)
      "accepted a forged typed/raw binding"
  let mut checkedMemory := false
  let mut checkedByteImage := false
  for (node,index) in nodes.toList.zipIdx do
    if let some (.memory image) := node.data then
      if !checkedMemory then
        let bad := {image with mutability := .unknown "fixture"}
        let changed := nodes.set! index {node with memory := some bad, data := some (.memory bad)}
        check (parseCompilerAllocIdWorld normalized changed ==
          .error "compact source memory has unknown mutability") "unknown mutability escaped pool checks"
        checkedMemory := true
      if !checkedByteImage && image.sizeBytes > 0 && image.mutability == .immutable &&
          image.alignBytes == 1 && image.relocations.isEmpty && image.initializationRanges.all (·.initialized) then
        let bad := {image with bytesHex := String.ofList (List.replicate (image.sizeBytes * 2) 'A')}
        let changed := nodes.set! index {node with memory := some bad, data := some (.memory bad)}
        check (parseCompilerAllocIdWorld normalized changed ==
          .error "compact source byte image is not canonical lowercase hexadecimal")
          "noncanonical byte key escaped pool checks"
        checkedByteImage := true
  check (checkedMemory && checkedByteImage) "fixture lacks memory/eligible-byte negative controls"
  IO.println "compact allocator world: complete legacy equality, exact raw binding and malformed inputs PASS"
