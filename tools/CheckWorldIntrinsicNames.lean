import Miri.Input.WorldIntrinsicTypeName
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
    let expected ← must ((← must (row.getObjVal? "intrinsic")).getStr?)
    let (actual,next) ← must ((WorldIntrinsicTypeName.query metadata 512 id).run world)
    world := next
    unless actual == expected do throw (IO.userError s!"World named type printer differs from pinned rustc: {actual} vs {expected}")
  unless rows.size == 12 && constructed == 12 do
    throw (IO.userError "named-type fixture lacks twelve novel cases")
  let some first := rows[0]? | throw (IO.userError "intrinsic options control missing")
  let term ← must (GenericMaterialCodec.readTerm 4096 (← must (first.getObjVal? "type")))
  let (id,finalWorld) ← must ((GenericInstantiationWorld.resolveType 512 term).run world)
  let expected ← must ((← must (first.getObjVal? "intrinsic")).getStr?)
  let noOptions := {metadata with source := {metadata.source with queries := {metadata.source.queries with
    session := {metadata.source.queries.session with printOptions := none}}}}
  let (actual,_) ← must ((WorldIntrinsicTypeName.query noOptions 512 id).run finalWorld)
  unless actual == expected do throw (IO.userError "intrinsic printing depends on diagnostic options")
  IO.println "PASS twelve novel structural/nominal intrinsic strings equal pinned rustc; allocation transport excluded"
