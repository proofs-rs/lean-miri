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
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected selective source and oracle")
  let decoded ← must (decodeJson (← IO.FS.readFile sourcePath))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let some checked := runtime.checkedMaterial | throw (IO.userError "checked source absent")
  let initial := TypeArena.World.ofCheckedMaterial checked
  let oracle ← readFixture oraclePath 12
  let some nominal := decoded.document.types.find? (·.display == "Novel")
    | throw (IO.userError "source nominal type absent")
  let some source := decoded.document.types.find? (·.display == "Deferred<u8>")
    | throw (IO.userError "source generic declaration absent")
  let .adt data := source.shape | throw (IO.userError "source is not an ADT")
  let some definition := decoded.document.definitions[data.definition]? | throw (IO.userError "physical definition absent")
  let ((id,pointer,tail),world) ← must ((do
    let id ← TypeArena.World.internType (.adt ⟨definition.crateIndex,definition.index⟩ #[.Type nominal.id])
    unless id >= initial.materialTypes.size do throw "selective ADT was already material"
    unless ← runtime.sizedInWorld id do throw "raw u32 trailing field failed Sized"
    let tail ← runtime.fieldTypeInWorld id 0 1
    let pointer ← TypeArena.World.internType (.rawPointer id .Not)
    pure (id,← runtime.layoutInWorld pointer,tail)) initial)
  check (tail == decoded.document.queries.primitives.u32) "requested trailing field returned wrong type"
  let some expected := oracle.types.find? (·.display == "*const Deferred<Novel>")
    | throw (IO.userError "independent pointer oracle absent")
  check (pointer.layout == (← oracle.lookup expected.id)) "selective pointer layout differs from pinned rustc"
  check (world.constructedTypes.size == 2) "Sized/requested tail eagerly instantiated unused function-pointer field"
  -- This unported function-pointer constructor is asked for only now. Its
  -- explicit failure must not prevent the preceding independent queries.
  check (!((runtime.fieldTypeInWorld id 0 0).run world).isOk)
    "fixture no longer isolates an unsupported unused field constructor"
  IO.println "PASS Sized, exact trailing-field type and new pointer layout avoid unrelated unsupported fn-pointer field; pointer equals pinned rustc"
