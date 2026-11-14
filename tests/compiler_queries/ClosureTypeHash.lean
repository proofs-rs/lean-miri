import Miri.Input.Decoder
import Miri.Input.WorldTypeHash

open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def number (row : Json) (key : String) : IO Nat := do
  let text ← must (row.getObjValAs? String key)
  let some value := text.toNat? | throw (IO.userError s!"invalid oracle {key}")
  check (value < 2^128) "oracle hash exceeds u128"
  pure value
private def component (bytes : ByteArray) (offset : Nat) : Nat :=
  (bytes.extract offset (offset + 16)).data.zipIdx.foldl
    (fun result (byte,index) => result + byte.toNat * 2^(8*index)) 0

private def corruptBound : Nat → GenericSubstitution.Term → Except String GenericSubstitution.Term
  | 0,_ => throw "closure corruption traversal exhausted"
  | _ + 1,.bound .region index variableIndex identity =>
    pure (.bound .region index (variableIndex + 19) identity)
  | fuel + 1,.binder variables body => do pure (.binder variables (← corruptBound fuel body))
  | fuel + 1,.node sort tag payload children => do pure (.node sort tag payload (← children.mapM (corruptBound fuel)))
  | fuel + 1,.definition sort tag identity children => do pure (.definition sort tag identity (← children.mapM (corruptBound fuel)))
  | _ + 1,term => pure term

-- Signature metadata is a JSON object; field order is not part of its syntax identity.
private def canonicalPayloads : Nat → GenericSubstitution.Term → Except String GenericSubstitution.Term
  | 0,_ => throw "closure canonicalization traversal exhausted"
  | fuel + 1,.binder variables body => do
    pure (.binder variables (← canonicalPayloads fuel body))
  | fuel + 1,.node sort tag payload children => do
    let payload ← if tag == "signature" then do
      pure (← Json.parse payload).compress
      else pure payload
    pure (.node sort tag payload (← children.mapM (canonicalPayloads fuel)))
  | fuel + 1,.definition sort tag identity children => do
    pure (.definition sort tag identity (← children.mapM (canonicalPayloads fuel)))
  | _ + 1,term => pure term

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected fresh closure source and independent compiler oracle")
  let source := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let types := source.types.map fun node =>
    {node with compilerFacts := node.compilerFacts.map fun facts => {facts with typeIdHash := none}}
  let mut material ← must (World.ofMaterial types source.typeConstants source.definitions source.predicates 8)
  let mut novel ← must (World.ofMaterial #[] #[] source.definitions #[] 8)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  check (rows.size == 9) "actual closure compiler oracle domain incomplete"
  let mut materialHits := 0
  let mut novelRows := 0
  let mut quantified := 0
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 16384 (← must (row.getObjVal? "type")))
    let expectedTree ← must (GenericMaterialCodec.readTerm 16384 (← must (row.getObjVal? "anonymized")))
    check ((← must (BinderRegions.eraseAndAnonymizeOpen 16384 term)) == expectedTree)
      "Closure whole-root region anonymization differs from compiler"
    if (← must (row.getObjValAs? Nat "signature_bound_variables")) > 0 then
      quantified := quantified + 1
    if (← must (row.getObjValAs? Nat "signature_bound_variables")) > 0 then
      let malformed ← must (corruptBound 16384 term)
      let result := do
        let (id,broken) ← (GenericInstantiationWorld.resolveType 16384 malformed).run novel
        WorldTypeHash.query broken 16384 id
      check (!result.isOk) "Closure out-of-bounds owned signature binder produced a hash"
    let expected ← number row "hash"
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 16384 term).run material)
    material := next
    let isNovel ← must (row.getObjValAs? Bool "novel")
    if isNovel then
      novelRows := novelRows + 1
      check (id >= material.materialTypes.size) "novel generic closure borrowed a material type identity"
    else
      check (id < material.materialTypes.size) "actual compiler closure missed its full material identity"
      materialHits := materialHits + 1
    check ((← must (WorldTypeHash.query material 16384 id)).toNat == expected)
      "raw Closure hash differs from independent compiler"
    let some bytes ← must (WorldTypeHash.sourceBytes material 16384 id)
      | throw (IO.userError "Closure source stream remained unsupported")
    check (bytes.size == 33 && bytes[0]?.any (·.toNat == 17)) "Closure TyKind stable stream has wrong shape"
    check (component bytes 1 == (← number row "definition_hash")) "Closure physical definition hash differs"
    check (component bytes 17 == (← number row "argument_hash")) "Closure complete generic/synthetic argument hash differs"
    let (fresh,next) ← must ((GenericInstantiationWorld.resolveType 16384 term).run novel)
    novel := next
    check ((← must (WorldTypeHash.query novel 16384 fresh)).toNat == expected)
      "raw novel Closure hash differs from independent compiler"
    check ((← must (canonicalPayloads 16384 (← must (GenericInstantiationWorld.ofType novel 16384 fresh)))) ==
      (← must (canonicalPayloads 16384 term)))
      "Closure raw syntax lost complete source arguments"
    let (again,next) ← must ((GenericInstantiationWorld.resolveType 16384 term).run novel)
    novel := next
    check (again == fresh) "Closure canonical source identity did not reuse dense execution node"
    check (!(WorldTypeHash.query novel 0 fresh).isOk) "Closure hash ignored fuel exhaustion"
    let .constructed (.closure owner arguments) ← must (novel.lookupType fresh)
      | throw (IO.userError "fresh Closure constructor absent")
    let reference ← must (novel.definitionRef owner)
    let some definition := source.definitions[reference]? | throw (IO.userError "Closure source definition absent")
    let some path := definition.rawPath | throw (IO.userError "Closure raw path absent")
    let header ← must (DefinitionPath.requireGenerics path)
    for changed in [none,some {path with genericHeader := none},
        some {path with genericHeader := some {header with parentParameterCount := header.parentParameterCount + 1}}] do
      let definitions := source.definitions.set! reference {definition with rawPath := changed}
      let broken ← must (World.ofMaterial #[] #[] definitions #[] 8)
      let result := do
        let (id,world) ← (GenericInstantiationWorld.resolveType 16384 term).run broken
        WorldTypeHash.query world 16384 id
      check (!result.isOk) "Closure missing/malformed raw owner header produced a hash"
    let (badMarker,wrong) ← must ((World.internType (.integer false .u8)).run novel)
    let malformedArgs := arguments.set! header.parentParameterCount (.Type badMarker)
    let (malformed,wrong) ← must ((World.internType (.closure owner malformedArgs)).run wrong)
    check (!(WorldTypeHash.query wrong 16384 malformed).isOk) "Closure invalid kind marker produced a hash"
    let truncated := arguments.extract 0 (arguments.size - 1)
    let (malformed,wrong) ← must ((World.internType (.closure owner truncated)).run novel)
    check (!(WorldTypeHash.query wrong 16384 malformed).isOk) "Closure incomplete synthetic arguments produced a hash"
  check (materialHits == 8 && novelRows == 1 && quantified >= 1) "Closure material/novel/region-binder coverage incomplete"
  check (novel.materialTypes.isEmpty && novel.materialConstants.isEmpty && novel.materialPredicates.isEmpty)
    "novel Closure hashing acquired material source/result rows"
  IO.println s!"PASS {rows.size} complete Closure component/root hashes, {materialHits} material identities and one novel generic closure; whole-root binders, empty prefixes, raw header/kind/arity/fuel controls"
