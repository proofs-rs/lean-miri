import Miri.Input.WorldTypeName
import Miri.Input.Decoder
open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
  let [source,oracle] := args | throw (IO.userError "expected fresh source.json oracle.json")
  let decoded ← must (decodeJson (← IO.FS.readFile source))
  let metadata ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let initial ← must (World.ofDocument decoded.document)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oracle))).getArr?)
  let mut world := initial
  let mut constructed := 0
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 512 term).run world)
    world := next
    if id >= world.materialTypes.size then constructed := constructed + 1
    let expected ← must ((← must (row.getObjVal? "display")).getStr?)
    let (actual,next) ← must ((WorldTypeName.query metadata 512 id).run world)
    world := next
    unless actual == expected do throw (IO.userError s!"World named type printer differs from pinned rustc: {actual} vs {expected}")
  unless rows.size == 12 && constructed == 12 do
    throw (IO.userError "named-type fixture lacks twelve novel cases")
  let some firstRow := rows[0]? | throw (IO.userError "named-type control lacks root")
  let firstTerm ← must (GenericMaterialCodec.readTerm 4096 (← must (firstRow.getObjVal? "type")))
  let bare ← must (World.ofMaterial world.materialTypes world.materialConstants
    (world.definitions.map fun definition => {definition with rawPath := none}) world.pointerBytes)
  let (first,bare) ← must ((GenericInstantiationWorld.resolveType 512 firstTerm).run bare)
  match (WorldTypeName.query metadata 512 first).run bare with
  | .error "named ADT printing requires raw definition path" => pure ()
  | .error error => throw (IO.userError s!"missing raw path failed for unrelated reason: {error}")
  | .ok _ => throw (IO.userError "missing raw definition path unexpectedly printed")
  IO.println "PASS twelve novel named/structural types equal independent pinned rustc Display; missing raw path fails closed"
