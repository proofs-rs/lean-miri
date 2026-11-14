import Miri.Input.Decoder
import Miri.Input.WorldTypeHash
import Miri.Input.WorldNormalization
import Miri.Input.WorldTypeFlags
open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def fingerprint (bytes : ByteArray) : Nat :=
  (bytes.extract 1 17).data.zipIdx.foldl (fun result (byte,index) => result + byte.toNat * 2^(8*index)) 0

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected independent dynamic source and oracle")
  let source := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let types := source.types.map fun node => {node with compilerFacts := node.compilerFacts.map fun facts => {facts with typeIdHash := none}}
  let mut material ← must (World.ofMaterial types source.typeConstants source.definitions source.predicates 8)
  let mut novel ← must (World.ofMaterial #[] #[] source.definitions #[] 8)
  let context ← must (AliasRuntime.Context.ofDocument source)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  check (rows.size == 8) "actual Dynamic oracle domain incomplete"
  let mut materialHits := 0
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    let expectedTree ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "anonymized")))
    check ((← must (BinderRegions.eraseAndAnonymizeOpen 4096 term)) == expectedTree)
      "dynamic whole-root anonymization differs from compiler"
    let text ← must (row.getObjValAs? String "hash")
    let some expected := text.toNat? | throw (IO.userError "invalid independent hash")
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run material)
    material := next
    if id < material.materialTypes.size then materialHits := materialHits + 1
    check ((← must (WorldTypeHash.query material 4096 id)).toNat == expected)
      "Dynamic raw material hash differs from compiler"
    let some bytes ← must (WorldTypeHash.sourceBytes material 4096 id)
      | throw (IO.userError "Dynamic raw syntax remained unsupported")
    let text ← must (row.getObjValAs? String "predicates")
    let some expectedPredicates := text.toNat? | throw (IO.userError "invalid predicate fingerprint")
    check (fingerprint bytes == expectedPredicates) "dynamic predicate component fingerprint differs"
    let (novelId,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run novel)
    novel := next
    check ((← must (WorldTypeHash.query novel 4096 novelId)).toNat == expected)
      "Dynamic raw novel hash differs from compiler"
    check ((← must (GenericInstantiationWorld.ofType novel 4096 novelId)) == term)
      "dynamic raw roundtrip lost source syntax"
    for key in #["has_erasable_regions","is_monomorphic","is_monomorphic_enough"] do
      let expectedFlag ← must (row.getObjValAs? Bool key)
      check ((← must (WorldTypeFlags.query novel key 4096 novelId)) == expectedFlag)
        s!"dynamic raw flag differs: {key}"
    let (normalizedId,next) ← must ((WorldNormalization.normalizeType context 4096 4096 novelId).run novel)
    novel := next
    check ((← must (GenericInstantiationWorld.ofType novel 4096 normalizedId)) == expectedTree)
      "dynamic runtime normalization differs from compiler whole-root tree"
    let (again,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run novel)
    novel := next
    check (again == novelId) "dynamic raw source interning failed to reuse identity"
    let blank ← must (World.ofMaterial #[] #[] (source.definitions.map fun definition => {definition with rawPath := none}) #[] 8)
    let result := do
      let (badId,broken) ← (GenericInstantiationWorld.resolveType 4096 term).run blank
      WorldTypeHash.query broken 4096 badId
    check (!result.isOk) "dynamic missing physical paths accepted"
    check (!(WorldTypeHash.query novel 0 novelId).isOk) "dynamic hash ignored traversal exhaustion"
  check (materialHits == 8) "actual Dynamic source keys missed complete material identities"
  check (novel.materialTypes.isEmpty && novel.materialConstants.isEmpty && novel.materialPredicates.isEmpty)
    "novel Dynamic acquired a material source/result pool"
  IO.println s!"PASS {rows.size} Dynamic component/root hashes in material and empty-prefix Worlds; whole-root binders, exact roundtrip/reuse, missing paths and fuel controls"
