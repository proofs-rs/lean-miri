import Miri.Input.Decoder
import Miri.Input.WorldInstanceName

open Lean Miri.Input
private def must {α} [ToString ε] : Except ε α → IO α
  | .ok value => pure value | .error error => throw (IO.userError (toString error))

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected fresh source and pinned instance display oracle")
  let document := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let mut world ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  for row in rows do
    let identity ← must (GenericMaterialCodec.readDefinition (← must (row.getObjVal? "definition")))
    let argument ← must (GenericMaterialCodec.readTerm 512 (← must (row.getObjVal? "argument")))
    let (ty,next) ← must ((RuntimeArrayTypes.liftType (GenericInstantiationWorld.resolveType 512 argument)).run world)
    world := next
    let definition ← must (world.arena.definitionRef identity)
    let (instanceId,next) ← must ((RuntimeArrayTypes.internInstance (.Item definition) #[.Type ty]).run world)
    world := next
    unless instanceId >= world.instances.material.size do throw (IO.userError "oracle instance was eagerly materialized")
    let key ← must (InstanceArena.Key.item world.arena identity #[.Type ty])
    let (actual,next) ← must ((WorldInstanceName.query 512 key).run world)
    world := next
    let expected ← must ((← must (row.getObjVal? "display")).getStr?)
    unless actual == expected do throw (IO.userError s!"novel instance display differs: {actual} vs {expected}")
  unless rows.size == 3 do throw (IO.userError "expected three novel instance names")
  IO.println "PASS three novel execution-owned Item instance names match pinned rustc Display without material name rows"
