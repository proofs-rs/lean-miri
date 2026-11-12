import Miri.Input.Decoder
import Miri.Input.WorldTypeHash

open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected fresh foreign source and compiler hash oracle")
  let source := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let mut world ← must (World.ofDocument source)
  let oracle ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  let some foreign := source.types.find? (fun node => node.shapeKind == .foreign)
    | throw (IO.userError "foreign source type absent")
  let .foreign reference := foreign.shape | throw (IO.userError "foreign source shape mismatch")
  let identity ← must (world.identity reference)
  let mut compared := 0
  for row in oracle do
    let display ← must ((← must (row.getObjVal? "display")).getStr?)
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run world)
    world := next
    if let .material node ← must (world.lookupType id) then
      if node.compilerFacts.any (fun facts => facts.typeIdHash.isSome) then
        throw (IO.userError "covered foreign/structural hash retained an eager result field")
    let expectedText ← must ((← must (row.getObjVal? "hash")).getStr?)
    let some expected := expectedText.toNat? | throw (IO.userError "invalid compiler hash decimal")
    let actual ← must (WorldTypeHash.query world 4096 id)
    unless actual.toNat == expected do throw (IO.userError s!"foreign structural hash differs from rustc: {display}")
    compared := compared + 1
  let blank ← must (World.ofMaterial #[] #[] source.definitions world.pointerBytes)
  let (novel,next) ← must ((World.internType (.foreign identity)).run blank)
  unless novel == 0 && next.materialTypes.isEmpty do throw (IO.userError "foreign constructor reused a material node")
  let actual ← must (WorldTypeHash.query next 4096 novel)
  unless actual == (← must (WorldTypeHash.query world 4096 foreign.id)) do
    throw (IO.userError "novel foreign identity hash depends on a type-result row")
  let definitions := source.definitions.map fun definition =>
    if definition.crateIndex == identity.crateIndex && definition.index == identity.index then
      {definition with rawPath := none} else definition
  let missing ← must (World.ofMaterial #[] #[] definitions world.pointerBytes)
  let (id,missing) ← must ((World.internType (.foreign identity)).run missing)
  if (WorldTypeHash.query missing 4096 id).isOk then
    throw (IO.userError "missing raw physical definition identity was accepted")
  unless compared >= 3 do throw (IO.userError "insufficient foreign/pointer hash oracle coverage")
  IO.println s!"PASS {compared} foreign/structural compiler hashes, novel foreign identity and missing-path controls"
