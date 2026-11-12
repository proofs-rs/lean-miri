import Miri.ABI.SequenceLayout
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
  let path :: candidates := args | throw (IO.userError "expected pinned baseline export [candidate]")
  let source ← readFixture path 12
  let mut arrays := 0
  let mut slices := 0
  let mut strings := 0
  for node in source.types do
    let actual ← match node.shape with
      | .array element _ constructor => do
        let element ← source.lookup element
        check (constructor.count < 2^64) "source array count exceeds u64"
        arrays := arrays + 1
        must (Miri.ABI.SequenceLayout.arrayLike source.target element (some (UInt64.ofNat constructor.count)))
      | .slice element => do
        slices := slices + 1
        must (Miri.ABI.SequenceLayout.slice source.target (← source.lookup element))
      | .str => do
        strings := strings + 1
        must (Miri.ABI.SequenceLayout.str source.target)
      | _ => continue
    let expected ← source.lookup node.id
    check (actual == expected) s!"sequence layout differs from pinned rustc: {node.display}\nexpected={repr expected}\nactual={repr actual}"
  check (arrays >= 6 && slices >= 2 && strings >= 1) "sequence oracle coverage incomplete"
  let byte ← must (Miri.ABI.PrimitiveLayout.compute source.target "u8")
  check (!(Miri.ABI.SequenceLayout.arrayLike source.target byte (some source.target.base.objSizeBound)).isOk)
    "sequence accepted exclusive object-size bound"
  IO.println s!"PASS {arrays} arrays, {slices} slices, {strings} str complete pinned layouts; overflow rejected"

  if let candidatePath :: _ := candidates then
    let candidate ← readFixture candidatePath 13
    let mut sequences := 0
    let mut pointers := 0
    for node in candidate.types do
      let some recipe := candidate.layouts[node.layoutId]? | throw (IO.userError "candidate layout absent")
      if recipe.sequenceType.isNone && recipe.pointerType.isNone then continue
      check (recipe.sizeBytes.isNone && recipe.abiAlignBytes.isNone &&
        recipe.fields.isNone && recipe.backendRepresentation.isNone)
        "candidate sequence/pointer retained eager layout results"
      let matching := source.types.filter (fun prior => prior.display == node.display && prior.shapeKind == node.shapeKind)
      check (!matching.isEmpty) s!"candidate recipe lacks pinned fixture correspondence: {node.display}"
      let actual ← candidate.lookup node.id
      for prior in matching do
        check (actual == (← source.lookup prior.id)) s!"source recipe differs from pinned rustc: {node.display}"
      if recipe.sequenceType.isSome then sequences := sequences + 1 else pointers := pointers + 1
    check (sequences >= 9 && pointers >= 2) "source recipe coverage incomplete"
    let some array := candidate.types.find? (fun node =>
      node.shapeKind == .array && (candidate.layouts[node.layoutId]?).any (·.sequenceType.isSome))
      | throw (IO.userError "canonical array recipe control absent")
    let .array element length identity := array.shape | throw (IO.userError "array control shape")
    let altered := candidate.types.set! array.id {array with shape := .array element length {identity with count := identity.count + 1}}
    check (!(RuntimeMetadata.resolveLayout candidate.target altered candidate.layouts array.layoutId
      candidate.definitions candidate.constants).isOk) "array accepted summarized count inconsistent with raw Value"
    let altered := candidate.types.set! array.id {array with shape := .array element candidate.constants.size identity}
    check (!(RuntimeMetadata.resolveLayout candidate.target altered candidate.layouts array.layoutId
      candidate.definitions candidate.constants).isOk) "array accepted missing raw length constant"
    let some scalar := candidate.types.find? (fun node => node.shapeKind == .bool)
      | throw (IO.userError "wrong sequence shape control absent")
    let some recipe := candidate.layouts[array.layoutId]? | throw (IO.userError "array control layout absent")
    let altered := candidate.layouts.set! array.layoutId {recipe with sequenceType := some scalar.id}
    check (!(RuntimeMetadata.resolveLayout candidate.target candidate.types altered array.layoutId
      candidate.definitions candidate.constants).isOk) "sequence recipe accepted scalar source type"
    check (!(JsonReader.run DecoderValues.parseLayout "{\"sequence_type\":0,\"pointer_type\":0}").isOk)
      "decoder accepted conflicting sequence and pointer recipes"
    check (!(JsonReader.run DecoderValues.parseLayout "{\"pointer_type\":0,\"size_bytes\":8}").isOk)
      "decoder accepted eager pointer size beside raw constructor"
    IO.println s!"PASS {sequences} source sequence and {pointers} pointer recipes equal complete pinned layouts; rawcount/missingconstant/wrongkind/conflicting/eager-result controls rejected"
