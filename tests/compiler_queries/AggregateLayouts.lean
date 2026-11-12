import Miri.ABI.UnivariantLayout
import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

private structure Fixture where
  target : Miri.ABI.RuntimeTargetDataLayout
  types : Array TypeNode
  layouts : Array Layout
  definitions : Array DefinitionId
  constants : Array Miri.MIR.TypeConst

/-- A focused source-derived adapter. It reads target/type/layout material
only, ignoring unrelated FnAbi/catalog sections without inventing their seeds.
No production decoder compatibility is introduced. -/
private def readFixture (path : String) (version : Nat) : IO Fixture := do
  let raw ← must (Json.parse (← IO.FS.readFile path))
  check ((← must ((← must (raw.getObjVal? "schema_version")).getNat?)) == version)
    "unexpected producer schema in differential input"
  let targetJson ← must (raw.getObjVal? "runtime_target_data_layout")
  let targetInput ← must (JsonReader.run CatalogDecoder.targetDataLayout targetJson.compress)
  let target ← must ((RuntimeMetadata.importTarget targetInput).mapError toString)
  let typeRows ← must ((← must (raw.getObjVal? "types")).getArr?)
  let mut types := #[]
  let mut skippedAliases := 0
  for row in typeRows do
    let shape ← must (row.getObjVal? "shape")
    let kind ← must ((← must (shape.getObjVal? "kind")).getStr?)
    -- The historical producer did not retain alias rigidity. This focused
    -- oracle cannot infer it; omit that shape and fail if a dependency needs it.
    if version == 12 && kind == "alias" then
      skippedAliases := skippedAliases + 1
      continue
    let fields ← must row.getObj?
    let row := Json.mkObj (fields.toList.filter (fun field => field.1 != "compiler_facts"))
    types := types.push (← must (JsonReader.run DecoderValues.parseTypeNode row.compress))
  if skippedAliases != 0 then IO.println s!"oracle scope: skipped {skippedAliases} historical alias shapes without rigidity"
  let values ← must ((← must (raw.getObjVal? "layout_values")).getArr?)
  let refs ← must ((← must (raw.getObjVal? "layouts")).getArr?)
  let layouts ← refs.mapM fun row => do
    let id ← must row.getNat?
    let some value := values[id]? | throw (IO.userError "layout value reference absent")
    must (JsonReader.run DecoderValues.parseLayout value.compress)
  let definitions ← (← must ((← must (raw.getObjVal? "definitions")).getArr?)).mapM fun row =>
    must (JsonReader.run (DecoderValues.parseDefinitionId "$.definitions") row.compress)
  let constants ← (← must ((← must (raw.getObjVal? "type_constants")).getArr?)).mapM fun row =>
    must (JsonReader.run (TypeConstCodec.decode "oracle.constant") row.compress)
  return ⟨target,types,layouts,definitions,constants⟩

private def Fixture.lookup (fixture : Fixture) (id : Nat) : IO Miri.ABI.LayoutData := do
  let some node := fixture.types.find? (·.id == id) | throw (IO.userError "type absent")
  must ((RuntimeMetadata.resolveLayout fixture.target fixture.types fixture.layouts node.layoutId fixture.definitions fixture.constants).mapError toString)

def main (args : List String) : IO Unit := do
  let path::candidatePaths := args | throw (IO.userError "expected pinned baseline export [candidate export]")
  check (!(JsonReader.run DecoderValues.parseLayout "{\"struct_type\":0,\"tuple_type\":0}").isOk)
    "struct decoder accepted conflicting recipe constructors"
  check (!(JsonReader.run DecoderValues.parseLayout "{\"struct_type\":0,\"size_bytes\":0}").isOk)
    "struct decoder accepted an eager size beside raw material"
  let source ← readFixture path 12
  let mut count := 0
  for node in source.types do
    let .tuple elements := node.shape | continue
    let fields ← elements.mapM source.lookup
    let expected ← source.lookup node.id
    let kind := if elements.isEmpty then Miri.ABI.UnivariantLayout.Kind.alwaysSized
      else .maybeUnsized
    let actual ← must (Miri.ABI.UnivariantLayout.compute source.target fields {} kind)
    check (actual == expected) s!"tuple univariant mismatch: {node.id}\nexpected={repr expected}\nactual={repr actual}"
    count := count + 1
  let mut structs := 0
  -- These named fixture declarations have no generic or unsized tail fields;
  -- their source caller selects AlwaysSized. This finite adapter is not a
  -- general inference of definition-level sizedness from instantiated fields.
  for node in source.types do
    unless ["C", "Packed", "Aligned", "Transparent", "Reordered", "ScalarPair", "Empty"].contains node.display do continue
    let .adt data := node.shape | throw (IO.userError "fixture struct shape mismatch")
    let some variant := data.variants[0]? | throw (IO.userError "fixture struct variant missing")
    let fields ← variant.fields.mapM (fun field => source.lookup field.typeId)
    let rawRepr := data.representation
    let representation : Miri.ABI.UnivariantLayout.Representation := {
      flags := UInt8.ofNat rawRepr.flagsBits, integerRepresentation := rawRepr.integer.isSome,
      align := ← rawRepr.alignBytes.mapM (fun bytes => must ((RuntimeMetadata.alignment bytes).mapError toString)),
      pack := ← rawRepr.packBytes.mapM (fun bytes => must ((RuntimeMetadata.alignment bytes).mapError toString)),
      fieldShuffleSeed := UInt64.ofNat rawRepr.fieldShuffleSeed }
    let actual ← must (Miri.ABI.UnivariantLayout.compute source.target fields representation .alwaysSized)
    let expected ← source.lookup node.id
    check (actual == expected) s!"struct univariant mismatch: {node.display}\nexpected={repr expected}\nactual={repr actual}"
    structs := structs + 1
  check (structs == 7) s!"fixture struct coverage incomplete: {structs}"
  check (count >= 1) "no tuple source oracle"
  IO.println s!"PASS {structs} complete struct layouts equal pinned rustc (C, packed, aligned, transparent, reordered, scalar pair, empty)"
  IO.println s!"PASS {count} complete tuple layouts equal pinned rustc"
  if let candidatePath::_ := candidatePaths then
    let candidate ← readFixture candidatePath 13
    check (candidate.target == source.target) "candidate aggregate target differs"
    let mut comparisons := 0
    for node in candidate.types do
      unless node.shapeKind == .tuple do continue
      let some recipe := candidate.layouts[node.layoutId]?
        | throw (IO.userError "candidate tuple layout absent")
      check (recipe.tupleType.isSome && recipe.fields.isNone &&
        recipe.backendRepresentation.isNone && recipe.sizeBytes.isNone)
        "candidate tuple retained eager layout results"
      -- This finite fixture has stable, unambiguous type spellings. They select
      -- corresponding oracle rows only; interpreter algorithms never use them.
      let matching := source.types.filter (fun prior =>
        prior.shapeKind == .tuple && prior.display == node.display)
      check (!matching.isEmpty) s!"candidate tuple lacks source fixture oracle: {node.display}"
      let actual ← candidate.lookup node.id
      for prior in matching do
        let expected ← source.lookup prior.id
        check (actual == expected) s!"tuple recipe differs from pinned rustc: {node.display}\nexpected={repr expected}\nactual={repr actual}"
      comparisons := comparisons + 1
    check (comparisons >= 8) s!"tuple recipe fixture coverage incomplete: {comparisons}"
    IO.println s!"PASS {comparisons} source tuple recipes equal complete pinned rustc layouts"
    let mut structRecipes := 0
    for node in candidate.types do
      let some recipe := candidate.layouts[node.layoutId]?
        | throw (IO.userError "candidate struct layout absent")
      if recipe.structType.isNone then continue
      check (recipe.structType.isSome && recipe.fields.isNone &&
        recipe.backendRepresentation.isNone && recipe.sizeBytes.isNone)
        "candidate struct retained eager layout results"
      let matching := source.types.filter (fun prior => prior.display == node.display)
      check (!matching.isEmpty) "struct recipe oracle absent"
      let actual ← candidate.lookup node.id
      for prior in matching do
        check (actual == (← source.lookup prior.id)) s!"struct recipe differs from pinned rustc: {node.display}"
      check (!(RuntimeMetadata.resolveLayout candidate.target candidate.types candidate.layouts
        node.layoutId #[] candidate.constants).isOk) "struct recipe accepted absent source declarations"
      let wrong := candidate.layouts.set! node.layoutId {recipe with structType := some candidate.types.size}
      check (!(RuntimeMetadata.resolveLayout candidate.target candidate.types wrong
        node.layoutId candidate.definitions candidate.constants).isOk) "struct recipe accepted absent raw type"
      structRecipes := structRecipes + 1
    check (structRecipes >= 7) s!"production struct recipe coverage incomplete: {structRecipes}"
    IO.println s!"PASS {structRecipes} source struct recipes equal complete pinned rustc layouts; missing declarations/types rejected"
