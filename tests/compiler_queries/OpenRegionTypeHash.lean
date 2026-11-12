import Miri.Input.Decoder
import Miri.Input.WorldTypeHash
open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected source and independent oracle")
  let source := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let mut material ← must (World.ofDocument source)
  let mut novel ← must (World.ofMaterial #[] #[] source.definitions material.pointerBytes)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  unless rows.size == 7 do throw (IO.userError "expected seven complete actual open-region hash keys")
  let mut missingPathRejections := 0
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    let expectedText ← must (row.getObjValAs? String "hash")
    let some expected := expectedText.toNat? | throw (IO.userError "invalid compiler hash decimal")
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run material)
    material := next
    let some _ ← must (WorldTypeHash.sourceBytes material 4096 id)
      | throw (IO.userError "open source raw hash remained unsupported")
    unless (← must (WorldTypeHash.query material 4096 id)).toNat == expected do
      throw (IO.userError "open material raw hash differs from compiler")
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run novel)
    novel := next
    let blank ← must (World.ofMaterial #[] #[] (novel.definitions.map (fun definition => { definition with rawPath := none })) novel.pointerBytes)
    let (brokenId,broken) ← must ((GenericInstantiationWorld.resolveType 4096 term).run blank)
    if !(WorldTypeHash.query broken 4096 brokenId).isOk then
      missingPathRejections := missingPathRejections + 1
    unless (← must (WorldTypeHash.query novel 4096 id)).toNat == expected do
      throw (IO.userError "open novel raw hash differs from compiler")
  unless missingPathRejections > 0 do throw (IO.userError "named escaping region did not require its physical definition path")
  IO.println s!"PASS {rows.size} complete open-region compiler hashes from material and empty-prefix worlds"
