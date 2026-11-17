import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

open Lean Miri.ABI Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def fieldAt (runtime : RuntimeMetadata) (strId index : Nat) : Except String (TyAndLayout TypeId) := do
  let parent ← (runtime.lookup strId).mapError toString
  (runtime.field parent index).mapError toString

private def withNodes (runtime : RuntimeMetadata) (nodes : Array TypeNode) : RuntimeMetadata :=
  { source := { runtime.source with types := nodes }, target := runtime.target }

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh str_field exporter input")
  let decoded ← must (decodeJson (← IO.FS.readFile path))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let some strNode := runtime.source.types.find? (·.shapeKind == .str)
    | throw (IO.userError "input contains no str type")
  let some u8Node := runtime.source.types.find? (fun node => node.shapeKind == .uint &&
    node.shapeMetadata.unsignedKind == some (.known .u8))
    | throw (IO.userError "input contains no canonical u8 type")
  let u8Layout ← must ((runtime.lookup u8Node.id).mapError toString)
  for index in #[0, 1, 7, 99] do
    let actual ← must (fieldAt runtime strNode.id index)
    check (actual.ty == u8Node.id && actual.layout == u8Layout.layout)
      s!"source str projection {index} lost its u8 result"
  let strLayout ← must ((runtime.lookup strNode.id).mapError toString)
  check (!strLayout.layout.isSized && strLayout.layout.fields.count == 0)
    "str source layout lost its unsized zero-length array shape"
  let absent := withNodes runtime (runtime.source.types.map fun node =>
    if node.id == u8Node.id then { node with shape := .never } else node)
  check (!(fieldAt absent strNode.id 0).isOk) "str field succeeded without a canonical u8 type"
  let ambiguous := withNodes runtime (runtime.source.types.push { u8Node with id := runtime.source.types.size })
  check (!(fieldAt ambiguous strNode.id 0).isOk) "str field succeeded with ambiguous u8 types"
  IO.println "str source field projection: canonical u8, unsized layout and missing/ambiguous primitive guards passed"
