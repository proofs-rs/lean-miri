import Miri.Input.Decoder
import Miri.Input.WorldTypeHash
open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def corruptBound : Nat → GenericSubstitution.Term → Except String GenericSubstitution.Term
  | 0,_ => throw "test corruption traversal exhausted"
  | fuel + 1,term => do
    match term with
    | .bound .region index _ identity => pure (.bound .region index 999 identity)
    | .binder variables body => pure (.binder variables (← corruptBound fuel body))
    | .node sort tag payload children => pure (.node sort tag payload (← children.mapM (corruptBound fuel)))
    | .definition sort tag identity children => pure (.definition sort tag identity (← children.mapM (corruptBound fuel)))
    | _ => pure term

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected fresh source and FnPtr/HRTB oracle")
  let source := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let base ← must (World.ofDocument source)
  let mut covered := 0
  for node in source.types do
    if node.shapeKind == .functionPointer then
      let some _ ← must (WorldTypeHash.sourceBytes base 4096 node.id) | continue
      if node.compilerFacts.any (fun facts => facts.typeIdHash.isSome) then
        throw (IO.userError "function-pointer source retained an eager hash answer")
      covered := covered + 1
  unless covered ≥ 11 do throw (IO.userError "fresh source lacks complete FnPtr/HRTB material domain")
  let mut world ← must (World.ofMaterial #[] #[] source.definitions base.pointerBytes)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  for row in rows do
    let display ← must (row.getObjValAs? String "display")
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    let anonymized ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "anonymized")))
    unless (← must (BinderRegions.eraseAndAnonymize 4096 term)) == anonymized do
      throw (IO.userError s!"raw HRTB anonymization differs: {display}")
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run world)
    world := next
    let expectedText ← must (row.getObjValAs? String "hash")
    let some expected := expectedText.toNat? | throw (IO.userError "invalid compiler hash")
    let value ← must (WorldTypeHash.query world 4096 id)
    unless value.toNat == expected do throw (IO.userError s!"raw FnPtr/HRTB hash differs: {display}")
  unless rows.size ≥ 11 do throw (IO.userError "FnPtr/HRTB differential domain incomplete")
  let some quantified := rows[4]? | throw (IO.userError "quantified source row absent")
  let term ← must (GenericMaterialCodec.readTerm 4096 (← must (quantified.getObjVal? "type")))
  let bad ← must (corruptBound 4096 term)
  match (GenericInstantiationWorld.resolveType 4096 bad).run world with
  | .error _ => pure ()
  | .ok (id,broken) =>
    if (WorldTypeHash.query broken 4096 id).isOk then
      throw (IO.userError "out-of-bounds higher-ranked variable was accepted")
  let some pointer := source.types.find? (fun node => node.shapeKind == .functionPointer)
    | throw (IO.userError "function-pointer source node absent")
  let .functionPointer signature variables := pointer.shape
    | throw (IO.userError "function-pointer source shape differs")
  let missingHeader := source.types.map fun node =>
    if node.id == pointer.id then
      {node with shape := .functionPointer {signature with rawSplatted := none} variables} else node
  let broken ← must (World.ofMaterial missingHeader source.typeConstants source.definitions base.pointerBytes)
  if (WorldTypeHash.query broken 4096 pointer.id).isOk then
    throw (IO.userError "missing raw function-pointer header was accepted")
  let badHeader := source.types.map fun node =>
    if node.id == pointer.id then
      {node with shape := .functionPointer {signature with rawSplatted := some (some 255)} variables} else node
  let broken ← must (World.ofMaterial badHeader source.typeConstants source.definitions base.pointerBytes)
  if (WorldTypeHash.query broken 4096 pointer.id).isOk then
    throw (IO.userError "function-pointer splatted sentinel was accepted as an index")
  IO.println s!"PASS {rows.size} FnPtr/HRTB compiler hashes/anonymized trees from an empty material prefix; malformed binder/header rejected"
