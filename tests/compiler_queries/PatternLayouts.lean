import Miri.ABI.PatternLayout
import Miri.Input.TypeConstCodec
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
  let path :: rest := args | throw (IO.userError "expected pinned pattern baseline and optional fresh production export")
  let raw ← must (Json.parse (← IO.FS.readFile path))
  let version ← must ((← must (raw.getObjVal? "schema_version")).getNat?)
  check ([12,13].contains version) "unexpected pinned oracle schema"
  let source ← readFixture path version
  let rows ← must ((← must (raw.getObjVal? "type_constants")).getArr?)
  let constants ← rows.mapM fun row => must (JsonReader.run (TypeConstCodec.decode "oracle.constant") row.compress)
  let scalar (id : Nat) : IO Miri.ABI.U128 := do
    let some (.Value _ tree) := constants[id]? | throw (IO.userError "range endpoint is not source value")
    let some (.Leaf bits _) := tree.nodes[tree.root]? | throw (IO.userError "range endpoint is not source scalar")
    check (bits < 2^128) "range endpoint exceeds u128"
    pure (BitVec.ofNat 128 bits)
  let mut ranges := 0
  let mut notNulls := 0
  let mut ors := 0
  for node in source.types do
    let .patternType base pattern := node.shape | continue
    let base ← source.lookup base
    let actual ← match pattern with
      | .range start finish => do
        ranges := ranges + 1
        must (Miri.ABI.PatternLayout.range source.target base (← scalar start) (← scalar finish))
      | .notNull => do
        notNulls := notNulls + 1
        must (Miri.ABI.PatternLayout.notNull source.target base)
      | .or patterns => do
        ors := ors + 1
        let intervals ← patterns.mapM fun pattern => do
          let .range start finish := pattern | throw (IO.userError "mixed Or oracle")
          pure (← scalar start, ← scalar finish)
        must (Miri.ABI.PatternLayout.orRanges source.target base intervals)
    let expected ← source.lookup node.id
    check (actual == expected) s!"pattern layout differs from pinned rustc: {node.display}\nexpected={repr expected}\nactual={repr actual}"
    -- Exercise the same production recipe resolver used for fresh documents;
    -- only the queried row changes, and the oracle remains the pinned snapshot.
    let recipeId := source.layouts.size
    let recipe : Layout := {
      patternType := some node.id
      kind := .layout
      maxReprAlignBytes := none, reprC := false, uninhabited := false
      largestNiche := none, randomizationSeed := 0, sizeBytes := none
      abiAlignBytes := none, unadjustedAbiAlignBytes := none
      fieldOffsetsBytes := .explicit #[], fields := none, variantsLayout := none
      backendRepresentation := none, variantsKind := none, backendReprKind := none
      variants := none, backendRepr := none }
    let candidate : Fixture := {source with
      types := source.types.map (fun (ty : TypeNode) => if ty.id == node.id then {ty with layoutId := recipeId} else ty)
      layouts := source.layouts.push recipe }
    let resolved ← candidate.lookup node.id
    check (resolved == expected) s!"production raw pattern recipe differs: {node.display}"
  check (ranges >= 3 && notNulls >= 2) "pattern fixture coverage incomplete"
  match rest with
  | [] => pure ()
  | [freshPath] =>
    let fresh ← must (decodeJson (← IO.FS.readFile freshPath))
    let metadata ← must ((RuntimeMetadata.ofDocument fresh.document).mapError toString)
    let mut checked := 0
    for node in metadata.source.types do
      let .patternType .. := node.shape | continue
      let some old := source.types.find? (·.display == node.display)
        | throw (IO.userError "fresh pattern has no pinned oracle")
      let some recipe := metadata.source.layouts[node.layoutId]?
        | throw (IO.userError "fresh pattern layout row absent")
      check (recipe.patternType == some node.id && recipe.sizeBytes.isNone)
        "fresh pattern producer retained an eager canonical layout"
      let expected ← source.lookup old.id
      let actual ← must ((metadata.lookup node.id).mapError toString)
      check (actual.layout == expected) s!"fresh production pattern layout differs: {node.display}"
      checked := checked + 1
    check (checked == ranges + notNulls + ors) "fresh production pattern fixture coverage incomplete"
  | _ => throw (IO.userError "unexpected arguments")
  let unsigned ← must (Miri.ABI.PrimitiveLayout.compute source.target "u8")
  let signed ← must (Miri.ABI.PrimitiveLayout.compute source.target "i8")
  check (!(Miri.ABI.PatternLayout.range source.target unsigned 9 1).isOk) "unsigned wrapping range accepted"
  check (!(Miri.ABI.PatternLayout.range source.target signed 127 128).isOk) "signed wrapping range accepted"
  let byte (value : Nat) : Miri.ABI.U128 := BitVec.ofNat 128 value
  check (!(Miri.ABI.PatternLayout.orRanges source.target unsigned #[(128,247),(7,127)]).isOk)
    "unsigned Or pattern accepted"
  check (!(Miri.ABI.PatternLayout.orRanges source.target signed #[(128,247)]).isOk)
    "one-range Or pattern accepted"
  check (!(Miri.ABI.PatternLayout.orRanges source.target signed #[(128,247),(byte 247,127)]).isOk)
    "overlapping Or ranges accepted"
  check (!(Miri.ABI.PatternLayout.orRanges source.target signed #[(128,247),(7,126)]).isOk)
    "Or range not ending at signed maximum accepted"
  check (!(JsonReader.run DecoderValues.parseLayout "{\"pattern_type\":0,\"pointer_type\":0}").isOk)
    "pattern recipe accepted another recipe"
  check (!(JsonReader.run DecoderValues.parseLayout "{\"pattern_type\":0,\"size_bytes\":1}").isOk)
    "pattern recipe accepted an eager answer"
  let unit ← must (Miri.ABI.UnivariantLayout.compute source.target #[] {} .alwaysSized)
  check (!(Miri.ABI.PatternLayout.notNull source.target unit).isOk) "nonscalar NotNull accepted"
  IO.println s!"PASS {ranges} range and {notNulls} NotNull and {ors} Or complete pinned layouts; signed/unsigned wrap and nonscalar controls rejected"
