import Miri.Input.CompilerThreadLocal
import Miri.Input.CompilerConstantQueries
import MiriTests.Connected.Proofs.RuntimeDocumentExact207

open Lean Miri.Input
open CompilerConstantQueries

-- Independent copies of the previous traversals retain their original array
-- concatenation and discarded-error behavior as finite comparison oracles.
private partial def referenceTls (j : Json) : Array Json :=
  let here := if (j.getObjValAs? String "kind").toOption == some "ThreadLocalRef" then #[j] else #[]
  match j with
  | .arr values => values.foldl (fun found value => found ++ referenceTls value) here
  | .obj values => values.toList.foldl (fun found entry => found ++ referenceTls entry.2) here
  | _ => here

private partial def referenceConstants (j : Json) (path : Array PathElement := #[]) :
    Array (Array PathElement × Json) :=
  if ((j.getObjVal? "constant").bind (fun c => c.getObjValAs? String "kind")).toOption == some "evaluated_const" then
    #[(path,j)]
  else match j with
  | .arr values => (values.mapIdx fun i value => referenceConstants value (path.push (.index i))).flatten
  | .obj fields => (fields.toList.toArray.map fun (name,value) =>
      referenceConstants value (path.push (.field name))).flatten
  | _ => #[]

private def check (j : Json) (label : String) : IO Unit := do
  let oldTls := referenceTls j
  let newTls := (CompilerThreadLocal.Rows.prepare j).values
  unless oldTls.map Json.compress == newTls.map Json.compress do
    throw (IO.userError s!"TLS occurrence/order changed: {label}")
  for pathPrefix in [#[], #[PathElement.field "prefix", .index 3]] do
    let old := referenceConstants j pathPrefix
    let new := constantOperands j pathPrefix
    unless old.size == new.size do throw (IO.userError s!"constant count changed: {label}")
    for (a,b) in old.zip new do
      unless decide (a.1 = b.1) && a.2.compress == b.2.compress do
        throw (IO.userError s!"constant preorder/path or stop-at-match changed: {label}")

private def checkSharedMemo (nodes : Array Json) (label : String) : IO Unit := do
  let reference := Id.run do
    let mut memo := DecoderValues.emptyDecodeMemo
    for (node,index) in nodes.toList.zipIdx do
      memo := DecoderValues.collectSharedDecodeMemo node s!"$.shared_payloads.nodes[{index}]" memo
    return memo
  let actual := DecoderValues.sharedDecodeMemo nodes
  for node in nodes do
    if DecoderValues.isSourceSpanJson node then
      unless reprStr (DecoderValues.parseSourceSpan node "$changed_occurrence" actual) ==
          reprStr (DecoderValues.parseSourceSpan node "$changed_occurrence" reference) do
        throw (IO.userError s!"shared span outcome or failure path changed: {label}")
    if DecoderValues.isLayoutPayload node then
      unless decide (DecoderValues.parseLayout node "$changed_occurrence" actual =
          DecoderValues.parseLayout node "$changed_occurrence" reference) do
        throw (IO.userError s!"shared layout outcome or failure path changed: {label}")

def main (args : List String) : IO Unit := do
  let tls := Json.mkObj [("kind", .str "ThreadLocalRef"), ("name", .str "日本語")]
  let operand := Json.mkObj [("constant", Json.mkObj [("kind", .str "evaluated_const")]),
    ("below", tls)]
  let nested := Json.mkObj [("constant", Json.mkObj [("kind", .str "evaluated_const")]),
    ("below", operand)]
  let cases := #[Json.null, .bool true, toJson (17 : Nat), .str "ThreadLocalRef",
    .arr #[], Json.mkObj [], tls, operand, nested,
    Json.mkObj [("constant", .bool true), ("kind", toJson (1 : Nat)), ("b", operand), ("a", tls)],
    Json.mkObj [("kind", .str "ThreadLocalRef"), ("below", .arr #[tls,tls])],
    Json.mkObj [("status", .str "debug_payload"), ("below", .arr #[tls,operand])],
    .arr (Array.replicate 1000 (Json.mkObj [("a", tls), ("b", operand), ("c", nested)])),
    .arr (Array.replicate 10000 (Json.mkObj [("kind", .str "inert"), ("constant", .null)]))]
  for i in [:cases.size] do
    check cases[i]! s!"handcrafted {i}"
    checkSharedMemo #[cases[i]!] s!"handcrafted {i}"
  let mut count := cases.size
  for argument in args do
    let path := System.FilePath.mk argument
    let paths ← if ← path.isDir then
        pure ((← path.readDir).filterMap fun entry =>
          if entry.path.extension == some "json" then some entry.path else none)
      else pure #[path]
    for path in paths do
      let bytes ← IO.FS.readBinFile path
      let parsed := if BinaryImage.hasMagic bytes then
          (JsonTraversalCache.resolveBinary bytes).map fun result => (result.1.root, result.1.nodes)
        else match String.fromUTF8? bytes with
          | some text => (Json.parse text).map fun value => (value, #[value])
          | none => .error "invalid UTF-8"
      let (value,nodes) ← match parsed with
        | .ok value => pure value
        | .error error => throw (IO.userError error)
      check value path.toString
      checkSharedMemo nodes path.toString
      count := count + 1
  IO.println s!"source walks/shared memos: TLS occurrences, constant paths/stop rules and span/layout outcomes PASS ({count} cases)"
