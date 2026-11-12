import Miri.ABI.UnionLayout
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
  return ⟨target,types,layouts,definitions⟩

private def Fixture.lookup (fixture : Fixture) (id : Nat) : IO Miri.ABI.LayoutData := do
  let some node := fixture.types.find? (·.id == id) | throw (IO.userError "type absent")
  must ((RuntimeMetadata.resolveLayout fixture.target fixture.types fixture.layouts node.layoutId fixture.definitions).mapError toString)

def main (args : List String) : IO Unit := do
  let path::candidatePaths := args | throw (IO.userError "expected pinned union baseline export [candidate export]")
  let source ← readFixture path 12
  let mut count := 0
  for node in source.types do
    let .adt data := node.shape | continue
    unless data.kind == .unionKind do continue
    let some variant := data.variants[0]? | throw (IO.userError "union variant absent")
    let fields ← variant.fields.mapM (fun field => source.lookup field.typeId)
    let rawRepr := data.representation
    let representation : Miri.ABI.UnivariantLayout.Representation := {
      flags := UInt8.ofNat rawRepr.flagsBits, integerRepresentation := rawRepr.integer.isSome,
      align := ← rawRepr.alignBytes.mapM (fun bytes => must ((RuntimeMetadata.alignment bytes).mapError toString)),
      pack := ← rawRepr.packBytes.mapM (fun bytes => must ((RuntimeMetadata.alignment bytes).mapError toString)),
      fieldShuffleSeed := UInt64.ofNat rawRepr.fieldShuffleSeed }
    let actual ← must (Miri.ABI.UnionLayout.compute source.target fields representation)
    let expected ← source.lookup node.id
    check (actual == expected) s!"union layout differs: {node.display}\nexpected={repr expected}\nactual={repr actual}"
    count := count + 1
  check (count >= 8) s!"union fixture coverage incomplete: {count}"
  check (!(Miri.ABI.UnionLayout.compute source.target #[]).isOk) "empty union accepted"
  let mut unsized ← must (Miri.ABI.PrimitiveLayout.compute source.target "u8")
  unsized := {unsized with backendRepr := .Memory (sized := false)}
  check (!(Miri.ABI.UnionLayout.compute source.target #[unsized]).isOk) "unsized union field accepted"
  IO.println s!"PASS {count} complete union layouts equal pinned rustc; empty and unsized unions rejected"
  if let candidatePath::_ := candidatePaths then
    let candidate ← readFixture candidatePath 13
    check (candidate.target == source.target) "union candidate target differs"
    for invalid in ["{\"union_type\":0,\"tuple_type\":0}",
        "{\"union_type\":0,\"primitive_recipe\":\"bool\"}",
        "{\"union_type\":0,\"size_bytes\":1}", "{\"union_type\":-1}"] do
      check (!(JsonReader.run DecoderValues.parseLayout invalid).isOk)
        "malformed union recipe was accepted"
    let mut comparisons := 0
    for node in candidate.types do
      let .adt data := node.shape | continue
      unless data.kind == .unionKind do continue
      let some recipe := candidate.layouts[node.layoutId]?
        | throw (IO.userError "candidate union recipe missing")
      check (recipe.unionType.isSome && recipe.sizeBytes.isNone &&
        recipe.fields.isNone && recipe.backendRepresentation.isNone)
        "union recipe retained eager layout results"
      let matching := source.types.filter (fun prior => prior.display == node.display)
      check (!matching.isEmpty) "source union fixture correspondence absent"
      let actual ← candidate.lookup node.id
      for prior in matching do
        let expected ← source.lookup prior.id
        check (actual == expected) s!"union recipe differs from pinned rustc: {node.display}"
      let wrong := candidate.layouts.set! node.layoutId
        {recipe with unionType := some candidate.types.size}
      check (!(RuntimeMetadata.resolveLayout candidate.target candidate.types wrong
        node.layoutId candidate.definitions).isOk) "union recipe accepted absent source type"
      let some nonUnion := candidate.types.find? (·.shapeKind == .bool)
        | throw (IO.userError "non-union control type absent")
      let wrong := candidate.layouts.set! node.layoutId
        {recipe with unionType := some nonUnion.id}
      check (!(RuntimeMetadata.resolveLayout candidate.target candidate.types wrong
        node.layoutId candidate.definitions).isOk) "union recipe accepted non-union source type"
      comparisons := comparisons + 1
    check (comparisons >= 8) "union recipe fixture coverage incomplete"
    IO.println s!"PASS {comparisons} raw union recipes equal complete pinned rustc layouts; invalid recipes rejected"
