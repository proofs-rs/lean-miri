import Miri.Input.Decoder
import Miri.Input.WorldTypeName
import Miri.Input.WorldIntrinsicTypeName

open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String A) : IO A :=
 match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
 let [source,oracle] := args | throw (IO.userError "expected source oracle")
 let document := (← must (decodeJson (← IO.FS.readFile source))).document
 let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
 let mut world ← must (World.ofDocument document)
 let rows ← must ((← must (Json.parse (← IO.FS.readFile oracle))).getArr?)
 for row in rows do
  let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
  let (id,next) ← must ((GenericInstantiationWorld.resolveType 512 term).run world)
  world := next
  unless id >= world.materialTypes.size do throw (IO.userError "function-pointer type was eager seeded")
  let reified ← must (GenericInstantiationWorld.ofType world 512 id)
  let (roundtrip,next) ← must ((GenericInstantiationWorld.resolveType 512 reified).run world)
  unless roundtrip == id do throw (IO.userError "FnPtr reify/resolve did not preserve identity")
  world := next
  let (actual,next) ← must ((WorldTypeName.query metadata 512 id).run world)
  world := next
  let expected ← must ((← must (row.getObjVal? "display")).getStr?)
  unless actual == expected do throw (IO.userError s!"diagnostic FnPtr differs: {actual} vs {expected}")
  let (actual,next) ← must ((WorldIntrinsicTypeName.query metadata 512 id).run world)
  world := next
  let expected ← must ((← must (row.getObjVal? "intrinsic")).getStr?)
  unless actual == expected do throw (IO.userError s!"intrinsic FnPtr differs: {actual} vs {expected}")
 unless rows.size == 6 do throw (IO.userError "expected six new function-pointer types")
 IO.println "PASS 12 pinned diagnostic/intrinsic strings across six novel function-pointer types"
