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

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected wrapper source and pinned oracle")
  let decoded ← must (decodeJson (← IO.FS.readFile sourcePath))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let some checked := runtime.checkedMaterial | throw (IO.userError "checked source prefix absent")
  let initial := TypeArena.World.ofCheckedMaterial checked
  let oracle ← readFixture oraclePath 12
  let some nominal := decoded.document.types.find? (·.display == "Novel")
    | throw (IO.userError "nominal source material absent")
  let mut success := 0
  for name in #["SizedWrapper","InheritedWrapper","MaybeWrapper"] do
    let some source := decoded.document.types.find? (·.display == name ++ "<u8>")
      | throw (IO.userError "raw wrapper source declaration absent")
    let .adt data := source.shape | throw (IO.userError "wrapper source is not an ADT")
    let some declaration := decoded.document.definitions[data.definition]?
      | throw (IO.userError "wrapper physical definition absent")
    let action : TypeArena.WorldM (Miri.ABI.TyAndLayout Nat) := do
      let id ← TypeArena.World.internType (.adt ⟨declaration.crateIndex,declaration.index⟩ #[.Type nominal.id])
      unless id >= initial.materialTypes.size do throw "novel wrapper was already material"
      runtime.layoutInWorld id
    let expectedName := name ++ "<Novel>"
    let some expected := oracle.types.find? (·.display == expectedName)
      | throw (IO.userError "wrapper independent rustc oracle absent")
    if name == "MaybeWrapper" then
      match action initial with
      | .ok _ => throw (IO.userError "unknown raw T:?Sized environment became a guessed layout kind")
      | .error reason =>
        check (reason == "term Sized requires a concrete type expression")
          s!"unsupported MaybeSized environment failed for unrelated reason: {reason}"
    else
      let (actual,_) ← must (action initial)
      check (actual.layout == (← oracle.lookup expected.id))
        s!"raw declaration Sized environment layout differs from rustc: {name}"
      success := success + 1
  check (success == 2) "direct and inherited Sized wrapper coverage incomplete"
  IO.println "PASS direct T:Sized and T:?Sized+Super:Sized new wrapper layouts equal complete rustc oracle; MaybeSized remains explicit unsupported"
