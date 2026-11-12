import Miri.Input.CompilerWorldFacts
import Miri.Input.Decoder
open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [source,oracle] := args | throw (IO.userError "expected fresh source.json oracle.json")
  let decoded ← must (decodeJson (← IO.FS.readFile source))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let context ← must (CompilerFacts.ofProgram runtime (← must (lowerProgram decoded.document)))
  let initial ← must (World.ofDocument decoded.document)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oracle))).getArr?)
  let mut world := initial
  let mut constructed := 0
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 512 term).run world)
    world := next
    if id >= world.materialTypes.size then constructed := constructed + 1
    for key in #["is_sized", "needs_drop", "opsem_inhabited"] do
      let expected ← must ((← must (row.getObjVal? key)).getBool?)
      let (actual,next) ← must ((CompilerFacts.booleanInWorld context id key).run world)
      world := next
      unless actual == expected do
        throw (IO.userError s!"World structural fact {key} type {id} differs from pinned rustc: {actual} vs {expected}")
  unless rows.size == 12 && constructed >= 9 do
    throw (IO.userError "structural fact fixture lacks twelve cases and nine novel types")
  IO.println s!"PASS {rows.size * 3} structural facts equal pinned rustc across {rows.size} cases, {constructed} novel types"
