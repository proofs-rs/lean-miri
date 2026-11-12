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
  let missingDefaults := {document with definitions := document.definitions.map fun definition =>
    {definition with rawPath := definition.rawPath.map fun path =>
      {path with parameterDefaultExpressions := none}} }
  let badWorld ← must (World.ofDocument missingDefaults)
  let (badId,badWorld) ← must ((GenericInstantiationWorld.resolveType 512 term).run badWorld)
  match (WorldTypeName.query metadata 512 badId).run badWorld with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError "missing raw generic default expressions were silently accepted")
  let (id,next) ← must ((GenericInstantiationWorld.resolveType 512 term).run world)
  world := next
  unless id >= world.materialTypes.size do throw (IO.userError "default argument type was eager seeded")
  let (actual,next) ← must ((WorldTypeName.query metadata 512 id).run world)
  world := next
  let expected ← must ((← must (row.getObjVal? "display")).getStr?)
  unless actual == expected do throw (IO.userError s!"diagnostic constant differs: {actual} vs {expected}")
  let (actual,next) ← must ((WorldIntrinsicTypeName.query metadata 512 id).run world)
  world := next
  let expected ← must ((← must (row.getObjVal? "intrinsic")).getStr?)
  unless actual == expected do throw (IO.userError s!"intrinsic constant differs: {actual} vs {expected}")
 unless rows.size == 5 do throw (IO.userError "expected five novel default-argument types")
 IO.println "PASS ten pinned diagnostic/intrinsic default argument spellings across five novel types"
