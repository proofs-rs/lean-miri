import Miri.Input.RuntimeArrayQueries
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
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected source and independent contextual oracle")
  let decoded ← must (decodeJson (← IO.FS.readFile sourcePath))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let oracle ← readFixture oraclePath 12
  let some mixed := decoded.document.types.find? (·.display == "Mixed")
    | throw (IO.userError "runtime Mixed source absent")
  let some prior := oracle.types.find? (·.display == "Mixed")
    | throw (IO.userError "runtime Mixed oracle absent")
  let raw ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← must ((← must (raw.getObjVal? "types")).getArr?)
  let some row := rows[prior.id]? | throw (IO.userError "Mixed oracle row absent")
  let queries ← must ((← must (row.getObjVal? "compiler_facts")).getObjVal? "projection_queries")
  let parents ← must ((← must (queries.getObjVal? "parents")).getArr?)
  let access : RuntimeArrayQueries.Access RuntimeArrayTypes.World := {get := id, set := fun _ value => value}
  let mut count := 0
  for (variant,index) in #[(1,0),(2,0),(2,1)] do
    let action : EStateM Miri.Interpreter.StepError RuntimeArrayTypes.World (Miri.ABI.TyAndLayout Nat) := do
      let parent ← RuntimeArrayQueries.layoutOf access mixed.id
      let selected ← RuntimeArrayQueries.perform access (runtime.variantLayoutInWorld parent variant)
      RuntimeArrayQueries.fieldLayout access selected index
    let actual ← match action initial with
      | .ok value _ => pure value
      | .error reason _ => throw (IO.userError s!"runtime selected-variant field failed: {reprStr reason}")
    let mut compared := false
    for parent in parents do
      let selected ← must (parent.getObjVal? "variant")
      unless selected == toJson variant do continue
      for field in ← must ((← must (parent.getObjVal? "fields")).getArr?) do
        unless (← must ((← must (field.getObjVal? "index")).getNat?)) == index do continue
        let layout ← must ((← must (field.getObjVal? "layout")).getNat?)
        let expected ← must ((RuntimeMetadata.resolveLayout oracle.target oracle.types oracle.layouts
          layout oracle.definitions oracle.constants).mapError toString)
        check (actual.layout == expected) s!"runtime wrapper discarded selected variant={variant}, field={index}"
        compared := true
    check compared "selected variant oracle field absent"
    count := count + 1
  IO.println s!"PASS {count} selected-variant field demands through actual RuntimeArrayQueries Access equal rustc u64/bool/u16 contexts"
