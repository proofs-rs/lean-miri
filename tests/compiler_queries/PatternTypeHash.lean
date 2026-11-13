import Miri.Input.Decoder
import Miri.Input.WorldTypeHash
open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected independent source and oracle")
  let source := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let types := source.types.map fun node => {node with compilerFacts := node.compilerFacts.map fun facts => {facts with typeIdHash := none}}
  let mut material ← must (World.ofMaterial types source.typeConstants source.definitions 8)
  let mut novel ← must (World.ofMaterial #[] #[] source.definitions 8)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  check (rows.size == 7) "actual Pattern oracle domain incomplete"
  let mut materialHits := 0
  let mut missingEndpoints := 0
  let mut missingPaths := 0
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    let text ← must (row.getObjValAs? String "hash")
    let some expected := text.toNat? | throw (IO.userError "invalid independent hash")
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run material)
    material := next
    if id < material.materialTypes.size then materialHits := materialHits + 1
    let some _ ← must (WorldTypeHash.sourceBytes material 4096 id)
      | throw (IO.userError "Pattern raw source remained unsupported")
    check ((← must (WorldTypeHash.query material 4096 id)).toNat == expected) "Pattern raw material hash differs from compiler"
    let constructor ← match ← must (material.lookupType id) with
      | .constructed constructor => pure constructor
      | .material node => do
        let some value ← must (material.materialKey node) | throw (IO.userError "raw Pattern constructor absent")
        pure value
    let .patternType _ pattern := constructor | throw (IO.userError "expected raw Pattern source")
    let some bytes ← must (WorldTypeHash.patternSourceBytes material 4096 pattern)
      | throw (IO.userError "raw Pattern component unsupported")
    let text ← must (row.getObjValAs? String "pattern_hash")
    let some expectedPattern := text.toNat? | throw (IO.userError "invalid independent Pattern fingerprint")
    check ((StableSipHash.hash bytes).toNat == expectedPattern) "Pattern component hash differs from compiler"

    let missing ← must (World.ofMaterial types #[] source.definitions 8)
    if id < types.size && !(WorldTypeHash.query missing 4096 id).isOk then missingEndpoints := missingEndpoints + 1
    let (novelId,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run novel)
    novel := next
    check ((← must (WorldTypeHash.query novel 4096 novelId)).toNat == expected) "Pattern raw novel hash differs from compiler"
    let blank ← must (World.ofMaterial #[] #[] (source.definitions.map fun definition => {definition with rawPath := none}) 8)
    let (badId,broken) ← must ((GenericInstantiationWorld.resolveType 4096 term).run blank)
    if !(WorldTypeHash.query broken 4096 badId).isOk then missingPaths := missingPaths + 1
    check (!(WorldTypeHash.query novel 0 novelId).isOk) "Pattern hash ignored traversal exhaustion"
  check (materialHits == 7) "actual Pattern keys did not match complete material identities"
  check (missingEndpoints >= 4) "Pattern ranges did not require original endpoint constants"
  check (missingPaths > 0) "named Pattern pointee did not require original physical paths"
  check (novel.materialTypes.isEmpty && novel.materialConstants.isEmpty) "novel Pattern acquired material prefixes"
  IO.println s!"PASS {rows.size} complete Pattern hashes from raw syntax in material and empty-prefix Worlds; eager hashes removed, missing endpoints/physical paths/fuel reject"
