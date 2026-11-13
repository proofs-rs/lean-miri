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
  predicates : Array VtablePredicate
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
  let predicates ← (← must ((← must (raw.getObjVal? "predicates")).getArr?)).mapM fun row =>
    must (JsonReader.run (DecoderValues.parseVtablePredicate "$.predicates") row.compress)
  return ⟨target,types,layouts,definitions,predicates,constants⟩

private def Fixture.lookup (fixture : Fixture) (id : Nat) : IO Miri.ABI.LayoutData := do
  let some node := fixture.types.find? (·.id == id) | throw (IO.userError "type absent")
  must ((RuntimeMetadata.resolveLayout fixture.target fixture.types fixture.layouts node.layoutId fixture.definitions fixture.constants fixture.predicates).mapError toString)

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
  let [baselinePath,candidatePath] := args | throw (IO.userError "expected baseline and candidate exports")
  let baseline ← readFixture baselinePath 12
  let candidate ← readFixture candidatePath 13
  let baselineRaw ← must (Json.parse (← IO.FS.readFile baselinePath))
  let candidateRaw ← must (Json.parse (← IO.FS.readFile candidatePath))
  let mut count := 0
  for node in candidate.types do
    let matching := baseline.types.filter (fun prior => prior.display == node.display && prior.shapeKind == node.shapeKind)
    for parent in ← pointerParents candidateRaw node.id do
      let variant ← must (parent.getObjVal? "variant")
      let fields ← must ((← must (parent.getObjVal? "fields")).getArr?)
      for field in fields do
        let index ← must ((← must (field.getObjVal? "index")).getNat?)
        let layoutId ← must ((← must (field.getObjVal? "layout")).getNat?)
        let actual ← must ((RuntimeMetadata.resolveLayout candidate.target candidate.types candidate.layouts
          layoutId candidate.definitions candidate.constants candidate.predicates).mapError toString)
        let mut compared := false
        for prior in matching do
          for oracleParent in ← pointerParents baselineRaw prior.id do
            unless (← must (oracleParent.getObjVal? "variant")) == variant do continue
            for oracleField in ← must ((← must (oracleParent.getObjVal? "fields")).getArr?) do
              unless (← must ((← must (oracleField.getObjVal? "index")).getNat?)) == index do continue
              let oracleLayout ← must ((← must (oracleField.getObjVal? "layout")).getNat?)
              let expected ← must ((RuntimeMetadata.resolveLayout baseline.target baseline.types baseline.layouts
                oracleLayout baseline.definitions baseline.constants baseline.predicates).mapError toString)
              check (actual == expected) s!"contextual field differs from pinned rustc: {node.display}, field={index}, variant={variant.compress}\nexpected={repr expected}\nactual={repr actual}"
              compared := true
        check compared s!"contextual field lacks exact source oracle: {node.display}, field={index}"
        count := count + 1
  IO.println s!"PASS {count} complete contextual field layouts equal pinned rustc"
  if let some niche := candidate.types.find? (·.display == "Niche") then
    let parents ← pointerParents candidateRaw niche.id
    let some parent := parents[0]? | throw (IO.userError "niche tag parent absent")
    let some field ← fieldZero? parent | throw (IO.userError "niche tag field absent")
    let tagId ← must ((← must (field.getObjVal? "layout")).getNat?)
    let some unsigned := candidate.types.find? (fun node => node.shapeMetadata.unsignedKind == some (.known .u8))
      | throw (IO.userError "canonical u8 control absent")
    check (tagId != unsigned.layoutId) "contextual full-range tag aliased canonical primitive request identity"
    let tag ← must ((RuntimeMetadata.resolveLayout candidate.target candidate.types candidate.layouts
      tagId candidate.definitions candidate.constants candidate.predicates).mapError toString)
    check (tag == (← candidate.lookup unsigned.id)) "full-range context control does not equal canonical primitive physically"
    let some recipe := candidate.layouts[tagId]? | throw (IO.userError "tag operation recipe absent")
    check (recipe.enumTagType == some niche.id) "tag operation does not retain original parent type"
    let some boolean := candidate.types.find? (·.shapeKind == .bool)
      | throw (IO.userError "malformed tag parent control absent")
    let corrupted := candidate.layouts.set! tagId {recipe with enumTagType := some boolean.id}
    check (!(RuntimeMetadata.resolveLayout candidate.target candidate.types corrupted tagId
      candidate.definitions candidate.constants candidate.predicates).isOk) "tag operation accepted a scalar parent without discriminant"
    check (!(JsonReader.run DecoderValues.parseLayout "{\"enum_tag_type\":0,\"primitive_recipe\":\"i8\"}").isOk)
      "decoder accepted tag operation and canonical primitive conflict"
    check (!(JsonReader.run DecoderValues.parseLayout "{\"enum_tag_type\":0,\"size_bytes\":1}").isOk)
      "decoder accepted eager tag layout beside source operation"
    IO.println "PASS equal-physical tag/canonical requests keep distinct identities; malformed parent/conflicting/eager-result controls rejected"
