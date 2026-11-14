import Miri.Input.Decoder
import Miri.Input.BinderRegions
import Miri.Input.WorldNormalization
import Miri.Input.WorldTypeName
import Miri.Input.WorldIntrinsicTypeName
import Miri.Input.WorldTypeFlags

open Lean Miri.Input Miri.Input.TypeArena Miri.Input.GenericSubstitution
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

-- FnSig payloads are JSON objects. Rust emits insertion order while Lean's
-- typed header reifier emits sorted keys; this adapter changes only key order.
private def canonicalHeaders : Nat → GenericSubstitution.Term → Except String GenericSubstitution.Term
  | 0, _ => throw "signature canonicalization exhausted"
  | fuel + 1, term => do
    match term with
    | .binder variables body => return .binder variables (← canonicalHeaders fuel body)
    | .node sort tag payload values =>
      let payload ← if sort == .aggregate && tag == "signature" then
        (Json.parse payload).map Json.compress else pure payload
      return .node sort tag payload (← values.mapM (canonicalHeaders fuel))
    | .definition sort tag identity values =>
      return .definition sort tag identity (← values.mapM (canonicalHeaders fuel))
    | _ => pure term

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected fresh source and independent binder oracle")
  let document := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let some target := document.runtimeTargetDataLayout | throw (IO.userError "missing raw target")
  -- A genuinely empty type/constant prefix prevents material ID or printer rows
  -- from certifying any case. Physical source definitions are retained exactly.
  let mut world ← must (World.ofMaterial #[] #[] document.definitions
    #[] target.defaultAddressSpacePointerSpec.pointerSizeBytes)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  unless rows.size == 9 do throw (IO.userError "incomplete higher-ranked FnPtr matrix")
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    let expected ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "normalized")))
    let actual ← must (BinderRegions.eraseAndAnonymize 4096 term)
    unless actual == expected do throw (IO.userError "whole-binder syntax differs from pinned rustc anonymization")
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run world)
    world := next
    unless world.materialTypes.isEmpty do throw (IO.userError "type query acquired a material prefix")
    for key in ["is_monomorphic","is_monomorphic_enough","has_erasable_regions"] do
      let expected ← must ((← must (row.getObjVal? key)).getBool?)
      unless (← must (WorldTypeFlags.query world key 4096 id)) == expected do
        throw (IO.userError s!"binder-aware type flag differs from rustc: {key}")
    let reified ← must (GenericInstantiationWorld.ofType world 4096 id)
    let (roundtrip,next) ← must ((GenericInstantiationWorld.resolveType 4096 reified).run world)
    unless roundtrip == id do throw (IO.userError "bound-variable constructor identity failed to roundtrip")
    world := next
    let (normal,next) ← must ((WorldNormalization.normalizeType metadata.normalizationContext 10000 4096 id).run world)
    world := next
    let actual ← must (GenericInstantiationWorld.ofType world 4096 normal)
    unless (← must (canonicalHeaders 4096 actual)) == (← must (canonicalHeaders 4096 expected)) do
      throw (IO.userError "runtime binder normalization differs from raw oracle")
    let (again,next) ← must ((WorldNormalization.normalizeType metadata.normalizationContext 10000 4096 normal).run world)
    unless again == normal do throw (IO.userError "binder normalization is not idempotent")
    world := next
    let (layout,next) ← must ((RuntimeMetadata.layoutInWorld metadata id).run world)
    world := next
    let target ← must ((RuntimeMetadata.importTarget target).mapError toString)
    unless layout.layout == (← must (Miri.ABI.PrimitiveLayout.compute target "fn_pointer")) do
      throw (IO.userError "higher-ranked FnPtr complete layout differs")
    for (ty,displayKey,intrinsicKey) in [(id,"display","intrinsic"),(normal,"normalized_display","normalized_intrinsic")] do
      let (actual,next) ← must ((WorldTypeName.query metadata 4096 ty).run world)
      world := next
      let expected ← must ((← must (row.getObjVal? displayKey)).getStr?)
      unless actual == expected do throw (IO.userError s!"higher-ranked diagnostic differs: {actual} / {expected}")
      let (actual,next) ← must ((WorldIntrinsicTypeName.query metadata 4096 ty).run world)
      world := next
      let expected ← must ((← must (row.getObjVal? intrinsicKey)).getStr?)
      unless actual == expected do throw (IO.userError s!"higher-ranked intrinsic differs: {actual} / {expected}")
  let some first := rows[0]? | throw (IO.userError "first binder oracle absent")
  let .node .type "function_pointer" "" (.cons (.binder _ body) .nil) ←
    must (GenericMaterialCodec.readTerm 4096 (← must (first.getObjVal? "type")))
    | throw (IO.userError "first oracle source shape differs")
  let malformed := Term.node .type "function_pointer" "" (.cons (.binder #[] body) .nil)
  unless !(BinderRegions.eraseAndAnonymize 4096 malformed).isOk do
    throw (IO.userError "missing owned variable was silently erased")
  let typeBound := Term.node .type "function_pointer" ""
    (.cons (.binder #[.type .anonymous] body) .nil)
  unless !((GenericInstantiationWorld.resolveType 4096 typeBound).run world).isOk do
    throw (IO.userError "unsupported type binder was accepted as a region binder")
  unless !(BinderRegions.eraseAndAnonymize 0 malformed).isOk do
    throw (IO.userError "exhausted binder normalization was accepted")
  IO.println "PASS 9 novel higher-ranked FnPtrs: exact whole normalization, 27 flags, 36 strings, complete layouts and malformed controls"
