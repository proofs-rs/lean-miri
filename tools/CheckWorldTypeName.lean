import Miri.Input.WorldTypeName
import Miri.Input.Decoder
open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def withOptions (metadata : RuntimeMetadata) (options : Option Catalog.PrintOptions) : RuntimeMetadata :=
  {metadata with source := {metadata.source with queries := {metadata.source.queries with
    session := {metadata.source.queries.session with printOptions := options}}}}
private def expectError (action : WorldM A) (world : World) (message : String) : IO Unit :=
  match action.run world with
  | .ok _ => throw (IO.userError "unsupported printer configuration returned a name")
  | .error actual => unless actual == message do throw (IO.userError s!"printer control failed for unrelated reason: {actual}")

def main (args : List String) : IO Unit := do
  let [source,oracle] := args | throw (IO.userError "expected fresh source.json oracle.json")
  let decoded ← must (decodeJson (← IO.FS.readFile source))
  let metadata ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let initial ← must (World.ofDocument decoded.document)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oracle))).getArr?)
  let mut world := initial
  let mut ids := #[]
  let mut constructed := 0
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 512 term).run world)
    world := next
    if id >= world.materialTypes.size then constructed := constructed + 1
    let expected ← must ((← must (row.getObjVal? "display")).getStr?)
    let (actual,next) ← must ((WorldTypeName.query metadata 512 id).run world)
    world := next
    unless actual == expected do throw (IO.userError s!"World type printer differs from pinned rustc: {actual} vs {expected}")
    ids := ids.push id
  unless rows.size == 10 && constructed >= 7 do throw (IO.userError "printer fixture lacks ten cases and seven novel structural types")
  let some array := ids[0]? | throw (IO.userError "printer array control absent")
  let some reference := ids[5]? | throw (IO.userError "printer reference control absent")
  let some options := metadata.source.queries.session.printOptions | throw (IO.userError "fresh print options absent")
  expectError (WorldTypeName.query (withOptions metadata none) 512 array) world
    "constructed type printing requires raw compiler print options"
  expectError (WorldTypeName.query (withOptions metadata (some {options with typeLengthLimit := 0})) 512 array) world
    "constructed type printer requires contextual truncation"
  expectError (WorldTypeName.query (withOptions metadata (some {options with verboseInternals := true})) 512 reference) world
    "verbose reference type printing is not implemented"
  IO.println s!"PASS {rows.size} structural type names equal pinned rustc, {constructed} newly constructed; missing/options/limit/verbose controls fail closed"
