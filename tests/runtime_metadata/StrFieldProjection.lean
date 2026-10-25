import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

open Lean Miri.ABI Miri.Input

private def requireIO (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def field (json : Json) (key : String) : Except String Json :=
  json.getObjVal? key

private def textField (json : Json) (key : String) : Except String String := do
  (← field json key).getStr?

private def natField (json : Json) (key : String) : Except String Nat := do
  (← field json key).getNat?

private def setField (json : Json) (key : String) (value : Json) : Except String Json := do
  match json with
  | .obj entries =>
    let retained := entries.toList.filter fun entry => entry.1 != key
    pure (Json.mkObj ((key, value) :: retained))
  | _ => throw "expected JSON object"

private def target : RuntimeTargetDataLayout := Id.run do
  let size : Size := ⟨8⟩
  let ptr : PointerSpec := ⟨size, .ONE, size, false⟩
  return ⟨⟨.little, .w64⟩, .ONE, .ONE, .ONE, .ONE, .ONE, .ONE,
    .ONE, .ONE, .ONE, .ONE, .ONE, #[], .ZERO, ptr, #[], .ZERO, .I32⟩

private def typeNode (record : Json) : Except String TypeNode := do
  let shape ← field record "shape"
  let shapeKind ← match ← textField shape "kind" with
    | "str" => pure .str
    | "uint" => pure .uint
    | kind => throw s!"unexpected retained type shape {kind}"
  let shapeMetadata : TypeShapeMetadata := {
    signedKind := none
    unsignedKind := if shapeKind == .uint then some (.known .u8) else none
    floatKind := none
    adtKind := none }
  let compilerFacts ← decodeTypeCompilerFacts (← field record "compiler_facts")
  let layout ← decodeCompilerLayout (← field record "layout")
  let status ← textField shape "status"
  unless status == "supported" do throw "retained type shape is not supported"
  return {
    id := ← natField record "type_id"
    display := ← textField record "display"
    shapeStatus := .supported
    shapeKind
    shapeMetadata
    signature := none
    layout
    compilerFacts := some compilerFacts
    payload := Json.mkObj [("shape", shape)] }

private def metadata (nodes : Array TypeNode) : Except String RuntimeMetadata := do
  let mut layouts := #[]
  for node in nodes do
    let layout ← (RuntimeMetadata.layout target node.layout).mapError toString
    layouts := layouts.push (node.id, .ok (⟨node.id, layout⟩ : TyAndLayout TypeId))
  let source : ImportDocument := {
    producer := ⟨"miri", "rustc", "version", "target"⟩
    completenessStatus := .supported
    types := nodes
    allocations := #[]
    instances := #[]
    selectedScope := none
    functionAbis := #[]
    bodies := #[]
    typedTree := .scalar .null
    obligations := #[]
    raw := .null }
  return {
    source := source
    target := target
    layouts := layouts
    nodeCache := some (RuntimeNodeLookupCache.build nodes)
    layoutCache := some (RuntimeLayoutLookupCache.build layouts)
  }

private def projectionValue (strLayout u8Layout : Json) : Json :=
  Json.mkObj [
    ("typing_env", toJson "fully_monomorphized"),
    ("parents", toJson #[Json.mkObj [
      ("layout", strLayout),
      ("fields", toJson #[Json.mkObj [
        ("index", toJson (0 : Nat)),
        ("type", Json.mkObj [("type_id", toJson (1 : Nat))]),
        ("layout", u8Layout)
      ]]),
      ("variant", Json.null)
    ]])
  ]

private def explicitStrRowZero (strRecord u8Record : Json) : Except String Json := do
  let facts ← field strRecord "compiler_facts"
  let projection := Json.mkObj [
    ("status", toJson "supported"),
    ("value", projectionValue (← field strRecord "layout") (← field u8Record "layout"))
  ]
  let facts ← setField facts "projection_queries" projection
  setField strRecord "compiler_facts" facts

private def fieldAt (runtime : RuntimeMetadata) (strId index : Nat) : Except String (TyAndLayout TypeId) := do
  let parent ← (runtime.lookup strId).mapError toString
  (runtime.field parent index).mapError toString

def main (args : List String) : IO Unit := do
  let strPath := args[0]?.getD "tests/runtime_metadata/fixtures/type155-159-raw-selected.json"
  let u8Path := args[1]?.getD "tests/runtime_metadata/fixtures/u8-raw-selected.json"
  let strText ← IO.FS.readFile strPath
  let u8Text ← IO.FS.readFile u8Path
  let strDocument ← requireIO (Json.parse strText)
  let u8Document ← requireIO (Json.parse u8Text)
  let strRecord ← match strDocument.getObjVal? "155" with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"missing retained Type155: {error}")
  let u8Records ← match u8Document.getArr? with
    | .ok records => pure records
    | .error error => throw (IO.userError s!"expected retained u8 record array: {error}")
  let u8Record ← match u8Records[0]? with
    | some value => pure value
    | none => throw (IO.userError "retained u8 record is missing")
  let strNode ← requireIO (typeNode strRecord)
  let u8Node ← requireIO (typeNode u8Record)
  let base ← requireIO (metadata #[strNode, u8Node])
  let u8Layout ← requireIO ((base.lookup u8Node.id).mapError toString)
  for index in [0, 7] do
    let actual ← requireIO (fieldAt base strNode.id index)
    check (actual.ty == u8Node.id && actual.layout == u8Layout.layout)
      s!"legacy null-query str field {index} did not resolve to canonical u8"

  let absent ← requireIO (metadata #[strNode])
  for index in [0, 7] do
    check (!(fieldAt absent strNode.id index).isOk)
      s!"str field {index} succeeded without a canonical u8 node"
  let duplicateU8 := {u8Node with id := 2}
  let ambiguous ← requireIO (metadata #[strNode, u8Node, duplicateU8])
  check (!(fieldAt ambiguous strNode.id 0).isOk)
    "str field succeeded with ambiguous supported canonical u8 nodes"

  let explicitRecord ← requireIO (explicitStrRowZero strRecord u8Record)
  let explicitStr ← requireIO (typeNode explicitRecord)
  let explicit ← requireIO (metadata #[explicitStr, u8Node])
  for index in [0, 1, 7, 99] do
    let actual ← requireIO (fieldAt explicit explicitStr.id index)
    check (actual.ty == u8Node.id && actual.layout == u8Layout.layout)
      s!"explicit str row-zero query did not map requested field {index} to u8"
  IO.println "str field projection: legacy fallback, exact u8 failures, and explicit row-zero mapping passed"
