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

private structure Built where
  adt : Miri.ABI.TyAndLayout Nat
  layouts : Array (Miri.ABI.TyAndLayout Nat)
  wide : Miri.ABI.TyAndLayout Nat
  data : Miri.ABI.TyAndLayout Nat
  metadata : Miri.ABI.TyAndLayout Nat

def main (args : List String) : IO Unit := do
  let [sourcePath, oraclePath] := args | throw (IO.userError "expected source-material and independent rustc oracle exports")
  let decoded ← must (decodeJson (← IO.FS.readFile sourcePath))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let initial ← must (TypeArena.World.ofDocument decoded.document)
  let oracle ← readFixture oraclePath 12
  let some nominal := decoded.document.types.find? (·.display == "Novel")
    | throw (IO.userError "nominal source declaration absent")
  let some generic := decoded.document.types.find? (·.display == "Generic<u8>")
    | throw (IO.userError "generic source declaration absent")
  let .adt data := generic.shape | throw (IO.userError "generic source is not an ADT")
  let some declaration := decoded.document.definitions[data.definition]?
    | throw (IO.userError "generic physical definition absent")
  let identity : GenericSubstitution.DefinitionIdentity := ⟨declaration.crateIndex,declaration.index⟩
  let expected (name : String) : IO Miri.ABI.LayoutData := do
    let some node := oracle.types.find? (·.display == name)
      | throw (IO.userError s!"independent rustc oracle absent: {name}")
    oracle.lookup node.id
  let (results, final) ← must ((do
    let adt ← TypeArena.World.internType (.adt identity #[.Type nominal.id])
    unless adt >= initial.materialTypes.size do throw "test ADT was already exported as a material type"
    let adtLayout ← runtime.layoutInWorld adt
    let array ← runtime.fieldLayoutInWorld adt 0
    unless array.ty >= initial.materialTypes.size do throw "test field array was already a material type"
    let raw ← TypeArena.World.internType (.rawPointer adt .Not)
    let reference ← TypeArena.World.internType (.reference adt .Not .Erased)
    let slice ← TypeArena.World.internType (.slice nominal.id)
    let sliceReference ← TypeArena.World.internType (.reference slice .Not .Erased)
    let tuple ← TypeArena.World.internType (.tuple #[adt,array.ty,raw,reference,sliceReference])
    let layouts ← #[adt,array.ty,raw,reference,sliceReference,tuple].mapM runtime.layoutInWorld
    let repeated ← TypeArena.World.internType (.adt identity #[.Type nominal.id])
    unless repeated == adt do throw "repeated nominal constructor changed execution identity"
    let wide ← runtime.layoutInWorld sliceReference
    let data ← runtime.fieldLayoutForInWorld wide 0
    let metadata ← runtime.fieldLayoutForInWorld wide 1
    pure ({adt := adtLayout,layouts,wide,data,metadata} : Built)) initial)
  let names := #["Generic<Novel>","[Novel; 3]","*const Generic<Novel>","&Generic<Novel>","&[Novel]",
    "(Generic<Novel>, [Novel; 3], *const Generic<Novel>, &Generic<Novel>, &[Novel])"]
  for (actual,name) in results.layouts.zip names do
    check (actual.layout == (← expected name)) s!"new execution type differs from independent rustc layout: {name}"
    check (actual.ty >= initial.materialTypes.size) s!"new execution type borrowed a source type ID: {name}"
  check (results.data.ty == results.wide.ty && results.data.layout.fields == .Primitive)
    "constructed wide data projection lost original Ty identity or retained fat fields"
  let some oracleWide := oracle.types.find? (·.display == "&[Novel]")
    | throw (IO.userError "wide pointer contextual oracle absent")
  let raw ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← must ((← must (raw.getObjVal? "types")).getArr?)
  let some row := rows[oracleWide.id]? | throw (IO.userError "wide oracle row absent")
  let facts ← must (row.getObjVal? "compiler_facts")
  let queries ← must (facts.getObjVal? "projection_queries")
  let parents ← must ((← must (queries.getObjVal? "parents")).getArr?)
  let some parent := parents[0]? | throw (IO.userError "wide oracle parent absent")
  let fields ← must ((← must (parent.getObjVal? "fields")).getArr?)
  for (actual,index) in #[(results.data,0),(results.metadata,1)] do
    let some field := fields[index]? | throw (IO.userError "wide oracle field absent")
    check ((← must ((← must (field.getObjVal? "index")).getNat?)) == index) "wide oracle field order mismatch"
    let layout ← must ((← must (field.getObjVal? "layout")).getNat?)
    let expected ← must ((RuntimeMetadata.resolveLayout oracle.target oracle.types oracle.layouts layout
      oracle.definitions oracle.constants).mapError toString)
    check (actual.layout == expected) s!"constructed wide pointer contextual field {index} differs from rustc"
  check (results.metadata.ty == decoded.document.queries.primitives.usize)
    "constructed slice metadata field did not return exact usize identity"
  check (final.constructedTypes.size >= 6) "new constructor graph did not persist in the execution universe"
  check (initial.constructedTypes.isEmpty && initial.constructedConstants.isEmpty) "query mutated the original execution value"
  check (!(runtime.lookup results.adt.ty).isOk) "pure source lookup accepted an execution-owned type ID"
  IO.println s!"PASS six genuinely new ADT/field-array/pointer/reference/slice-reference/tuple layouts equal independent rustc; {final.constructedTypes.size} persisted dense constructor nodes; both contextual wide-pointer fields match exact rustc oracle"

  -- Synthetic postdecode corruption: source field identity must agree with
  -- the original declaration, not merely have enough layout inputs to run.
  let some original := data.variants[0]? | throw (IO.userError "source struct variant absent")
  check (!original.fields.isEmpty) "field-domain corruption fixture is empty"
  let badVariant := {original with fields := original.fields.pop}
  let badShape := {data with variants := data.variants.set! 0 badVariant}
  let invalid := {generic with shape := .adt badShape}
  let badDocument := {decoded.document with types := decoded.document.types.set! generic.id invalid}
  let badRuntime ← must ((RuntimeMetadata.ofDocument badDocument).mapError toString)
  let badWorld ← must (TypeArena.World.ofDocument badDocument)
  match (badRuntime.layoutInWorld generic.id).run badWorld with
  | .ok _ => throw (IO.userError "layout accepted field domain inconsistent with declaration")
  | .error reason =>
    check (reason == "layout ADT field domain differs from raw declaration")
      s!"field-domain corruption failed for unrelated reason: {reason}"
  let some phantom := decoded.document.definitions.find? (fun definition =>
      definition.adtDeclaration.any (·.langItem == some "phantom_data"))
    | throw (IO.userError "canonical PhantomData raw declaration absent")
  let wrong : TypeArena.WorldM (Miri.ABI.TyAndLayout Nat) := do
    let id ← TypeArena.World.internType (.adt ⟨phantom.crateIndex,phantom.index⟩ #[])
    runtime.layoutInWorld id
  match wrong initial with
  | .ok _ => throw (IO.userError "empty ADT layout accepted incomplete nominal generic arguments")
  | .error reason => check (reason.contains "arity") s!"nominal arity control failed for unrelated reason: {reason}"
  IO.println "PASS declaration-domain corruption and empty-ADT missing generic argument controls"
