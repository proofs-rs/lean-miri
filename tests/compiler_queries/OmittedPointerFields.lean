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
    if version == 12 && (kind == "alias" || kind == "function_definition") then
      skippedAliases := skippedAliases + 1
      continue
    let fields ← must row.getObj?
    let row := Json.mkObj (fields.toList.filter (fun field => field.1 != "compiler_facts"))
    types := types.push (← must (JsonReader.run DecoderValues.parseTypeNode row.compress))
  if skippedAliases != 0 then IO.println s!"oracle scope: skipped {skippedAliases} historical alias/FnDef shapes without required source witnesses"
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

private def pointerParents (raw : Json) (id : Nat) : IO (Array Json) := do
  let rows ← must ((← must (raw.getObjVal? "types")).getArr?)
  let some row := rows[id]? | throw (IO.userError "pointer type row absent")
  let facts ← must (row.getObjVal? "compiler_facts")
  let queries ← must (facts.getObjVal? "projection_queries")
  if queries == .null then return #[]
  must ((← must (queries.getObjVal? "parents")).getArr?)

private def fieldZero? (parent : Json) : IO (Option Json) := do
  let fields ← must ((← must (parent.getObjVal? "fields")).getArr?)
  let mut result := none
  for field in fields do
    if (← must ((← must (field.getObjVal? "index")).getNat?)) == 0 then result := some field
  pure result

def main (args : List String) : IO Unit := do
  let [baselinePath,candidatePath] := args | throw (IO.userError "expected oracle and omitted-catalog candidate")
  let baseline ← readFixture baselinePath 12
  let baselineRaw ← must (Json.parse (← IO.FS.readFile baselinePath))
  let decoded ← must ((decodeJson (← IO.FS.readFile candidatePath)))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let some checked := runtime.checkedMaterial | throw (IO.userError "checked prefix missing")
  let initial := TypeArena.World.ofCheckedMaterial checked
  let mut count := 0
  for node in decoded.document.types do
    unless node.shapeKind == .rawPointer || node.shapeKind == .reference do continue
    if node.compilerFacts.any (fun facts => facts.projectionQueries.isSome) then continue
    let (parent,world) ← must ((runtime.layoutInWorld node.id).run initial)
    unless parent.layout.fields.count > 0 do continue
    let matching := baseline.types.filter (fun prior => prior.display == node.display && prior.shapeKind == node.shapeKind)
    check (!matching.isEmpty) s!"missing independent pointer oracle: {node.display}"
    for index in [:parent.layout.fields.count] do
      let (actual,_) ← must ((runtime.fieldLayoutForInWorld parent index).run world)
      if index == 0 then check (actual.ty == node.id) "data field lost wide parent identity"
      let mut compared := false
      for prior in matching do
        for oracleParent in ← pointerParents baselineRaw prior.id do
          let fields ← must ((← must (oracleParent.getObjVal? "fields")).getArr?)
          for field in fields do
            unless (← must ((← must (field.getObjVal? "index")).getNat?)) == index do continue
            let layoutId ← must ((← must (field.getObjVal? "layout")).getNat?)
            let expected ← must ((RuntimeMetadata.resolveLayout baseline.target baseline.types baseline.layouts
              layoutId baseline.definitions baseline.constants).mapError toString)
            check (actual.layout == expected) s!"omitted pointer field differs from rustc: {node.display} field {index}"
            compared := true
      check compared "missing independent field oracle"
      count := count + 1
  let mut strings := 0
  for node in decoded.document.types do
    unless node.shapeKind == .str do continue
    check (!(node.compilerFacts.any (fun facts => facts.projectionQueries.isSome))) "str projection catalog was retained"
    let (parent,world) ← must ((runtime.layoutInWorld node.id).run initial)
    let (actual,world) ← must ((runtime.fieldLayoutForInWorld parent 777).run world)
    let .material child ← must (world.lookupType actual.ty) | throw (IO.userError "str field primitive identity was not canonical material")
    check (child.shapeMetadata.unsignedKind == some (.known .u8)) "str field did not return canonical u8"
    let some prior := baseline.types.find? (·.shapeKind == .str) | throw (IO.userError "independent str source absent")
    for oracleParent in ← pointerParents baselineRaw prior.id do
      let some field ← fieldZero? oracleParent | throw (IO.userError "independent str field absent")
      let layoutId ← must ((← must (field.getObjVal? "layout")).getNat?)
      let expected ← must ((RuntimeMetadata.resolveLayout baseline.target baseline.types baseline.layouts
        layoutId baseline.definitions baseline.constants).mapError toString)
      check (actual.layout == expected) "str field special operation differs from rustc"
    strings := strings + 1
  check (strings > 0) "missing str projection omission control"
  IO.println s!"PASS {strings} str field special operations ignore field index exactly and return independent rustc u8 layout without projection catalogs"
  check (count >= 4) s!"insufficient omitted wide-pointer contexts: {count}"
  IO.println s!"PASS {count} actual wide pointer fields without exported projection catalogs equal independent rustc; data field preserves parent Ty"
