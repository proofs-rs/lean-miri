import Miri.Input.Decoder
import Miri.Input.RuntimeArrayQueries
open Lean Miri.Input Miri.ABI
private def must [ToString ε] (value : Except ε A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError (toString error))
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def negative (runtime : RuntimeMetadata) (world : TypeArena.World)
    (parent : TyAndLayout Nat) (index : Nat) (expected : String) : IO Unit := do
  match (RuntimeMetadata.variantLayoutInWorld runtime parent index).run world with
  | .error error => check (error == expected) s!"wrong variant residual: {error}; expected {expected}"
  | .ok _ => throw (IO.userError s!"invalid variant accepted: {expected}")

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath,countText] := args | throw (IO.userError "expected exact source, oracle and variant count")
  let some expectedCount := countText.toNat? | throw (IO.userError "expected explicit variant count")
  let original := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let document := {original with types := original.types.map fun node =>
    {node with compilerFacts := node.compilerFacts.map fun facts => {facts with projectionQueries := none}}}
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let some checked := runtime.checkedMaterial | throw (IO.userError "checked source absent")
  let materialWorld := TypeArena.World.ofCheckedMaterial checked
  let empty ← must (TypeArena.World.ofMaterial #[] #[] document.definitions #[] runtime.target.pointerSize.bytes.toNat)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  let mut compared := 0
  let mut emptyStates := 0
  let mut pruned := 0
  for row in rows do
    let term ← must (GenericMaterialCodec.readTerm 16384 (← must (row.getObjVal? "source_type")))
    let variants ← must ((← must (row.getObjVal? "variants")).getArr?)
    let (materialId,material) ← must ((GenericInstantiationWorld.resolveType 16384 term).run materialWorld)
    check (materialId < materialWorld.materialTypes.size) "oracle enum is not an actual material source type"
    let (freshId,fresh) ← must ((GenericInstantiationWorld.resolveType 16384 term).run empty)
    for (id,world) in #[(materialId,material),(freshId,fresh)] do
      let (parent,world) ← must ((RuntimeMetadata.layoutInWorld runtime id).run world)
      if variants.isEmpty then
        negative runtime world parent 0 "for_variant called on zero-variant enum"
      for variant in variants do
        let index ← must (variant.getObjValAs? Nat "index")
        let rawLayout ← must (variant.getObjVal? "layout")
        let expectedSeed ← must (JsonReader.run DecoderValues.parseLayout rawLayout.compress)
        let expected ← must ((RuntimeMetadata.layout runtime.target expectedSeed).mapError toString)
        let (actual,after) ← must ((RuntimeMetadata.variantLayoutInWorld runtime parent index).run world)
        check (actual.ty == id && actual.layout == expected) "complete source for_variant differs from independent compiler"
        check (actual.layout.variants == .Single index) "variant projection reentered whole Multiple enum"
        let (again,_) ← must ((RuntimeMetadata.variantLayoutInWorld runtime actual index).run after)
        check (again == actual) "same selected variant was not idempotent"
        match parent.layout.variants with
        | .Multiple tag encoding field layouts =>
          if layouts.size > 1 then
            negative runtime after actual ((index+1)%layouts.size) "cannot apply for_variant twice to a selected parent"
          negative runtime world {parent with layout := {parent.layout with variants := .Multiple tag encoding field #[]}}
            0 "variant index absent"
          negative runtime world parent layouts.size "variant index absent"
        | .Single inhabited =>
          if inhabited != index then pruned := pruned+1
          negative runtime world parent variants.size "variant index absent"
        | .Empty =>
          pruned := pruned+1
          negative runtime world parent variants.size "variant index absent"
        if actual.layout.fields.count == 0 then emptyStates := emptyStates+1
        if id == freshId && world.materialTypes.isEmpty then
          check (after.materialTypes.isEmpty && after.materialConstants.isEmpty && after.materialPredicates.isEmpty)
            "constructed variant query acquired copied prefixes"
        compared := compared+1
  check (compared == 2*expectedCount && emptyStates >= 10) "actual variant control domain changed"
  IO.println s!"PASS {compared} complete source variants (material+constructed), no projection rows; {emptyStates} empty variants, {pruned} pruned variants; Single idempotence/wrong-index/malformed bounds guards"
