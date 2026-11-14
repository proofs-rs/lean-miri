import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

open Lean Miri.Input Miri.ABI

private def must (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

private structure Oracle where
  target : RuntimeTargetDataLayout
  types : Array TypeNode
  layouts : Array Miri.Input.Layout
  definitions : Array DefinitionId
  predicates : Array VtablePredicate
  constants : Array Miri.MIR.TypeConst

/-- Focused historical producer adapter: read raw type identity and actual
layout records, not old executable/catalog protocols or ADT declaration schema.
Only physical definition identity is needed to compare these closed type keys. -/
private def readOracle (path : String) : IO Oracle := do
  let raw ← must (Json.parse (← IO.FS.readFile path))
  let target ← must (JsonReader.run CatalogDecoder.targetDataLayout
    (← must (raw.getObjVal? "runtime_target_data_layout")).compress)
  let target ← must ((RuntimeMetadata.importTarget target).mapError toString)
  let types ← (← must ((← must (raw.getObjVal? "types")).getArr?)).mapM fun row => do
    let fields ← must row.getObj?
    let row := Json.mkObj (fields.toList.filter (fun field => field.1 != "compiler_facts"))
    must (JsonReader.run DecoderValues.parseTypeNode row.compress)
  let definitions ← (← must ((← must (raw.getObjVal? "definitions")).getArr?)).mapM fun row => do
    pure ({
      crateIndex := ← must ((← must (row.getObjVal? "crate")).getNat?)
      index := ← must ((← must (row.getObjVal? "index")).getNat?) } : DefinitionId)
  let values ← must ((← must (raw.getObjVal? "layout_values")).getArr?)
  let layouts ← (← must ((← must (raw.getObjVal? "layouts")).getArr?)).mapM fun row => do
    let index ← must row.getNat?
    let some value := values[index]? | throw (IO.userError "oracle layout reference absent")
    must (JsonReader.run DecoderValues.parseLayout value.compress)
  let constants ← (← must ((← must (raw.getObjVal? "type_constants")).getArr?)).mapM fun row =>
    must (JsonReader.run (TypeConstCodec.decode "oracle.constant") row.compress)
  let predicates ← (← must ((← must (raw.getObjVal? "predicates")).getArr?)).mapM fun row =>
    must (JsonReader.run (DecoderValues.parseVtablePredicate "$.predicates") row.compress)
  pure ⟨target,types,layouts,definitions,predicates,constants⟩

private def Oracle.layout (oracle : Oracle) (node : TypeNode) : IO LayoutData :=
  must ((RuntimeMetadata.resolveLayout oracle.target oracle.types oracle.layouts node.layoutId
    oracle.definitions oracle.constants oracle.predicates).mapError toString)

private def internNovelEnum (identity : GenericSubstitution.DefinitionIdentity)
    (initial : TypeArena.World) : IO (TypeId × TypeArena.World) := do
  let mut world := initial
  let (byte,after) ← must ((TypeArena.World.internType (.integer false .u8)).run world)
  world := after
  let (usize,after) ← must ((TypeArena.World.internType (.integer false .usize)).run world)
  world := after
  let (count,after) ← must ((TypeArena.World.internConstant
    (.Value usize ⟨#[.Leaf 1031 world.pointerBytes],0⟩)).run world)
  world := after
  let (array,after) ← must ((TypeArena.World.internType (.array byte count)).run world)
  world := after
  let (enumId,after) ← must ((TypeArena.World.internType (.adt identity #[.Type array])).run world)
  world := after
  pure (enumId,world)

def main (args : List String) : IO Unit := do
  let [oraclePath,candidatePath,basePath] := args
    | throw (IO.userError "expected frozen compiler oracle, fresh enum candidate and fresh base")
  let oracle ← readOracle oraclePath
  let oracleWorld ← must (TypeArena.World.ofMaterial oracle.types oracle.constants oracle.definitions
    oracle.predicates oracle.target.pointerSize.bytes.toNat)
  let candidate := (← must (decodeJson (← IO.FS.readFile candidatePath))).document
  let metadata ← must ((RuntimeMetadata.ofDocument candidate).mapError toString)
  let sourceOnly : RuntimeMetadata := {metadata with source := {metadata.source with layouts := #[]}}
  let world ← must (TypeArena.World.ofDocument candidate)
  let mut compared := 0
  let mut residuals := 0
  let mut sourceDynamic := 0
  for node in candidate.types do
    let .adt adt := node.shape | continue
    unless adt.kind == .enumKind do continue
    let identity ← must (world.identity adt.definition)
    unless identity.crateIndex == 0 do continue
    let some seed := candidate.layouts[node.layoutId]? | throw (IO.userError "enum seed absent")
    let key ← must (GenericInstantiationWorld.ofType world 16384 node.id)
    let matching ← oracle.types.filterM fun old => do
      let .adt oldAdt := old.shape | return false
      unless (← must (oracleWorld.identity oldAdt.definition)) == identity do return false
      pure ((← must (GenericInstantiationWorld.ofType oracleWorld 16384 old.id)) == key)
    let some old := matching[0]? | throw (IO.userError "typed enum compiler oracle absent")
    let expected ← oracle.layout old
    let (actual,_) ← must ((RuntimeMetadata.layoutInWorld metadata node.id).run world)
    check (actual.layout == expected) s!"complete enum layout differs from pinned compiler: {node.display}"
    if seed.enumType.isSome then
      check (seed.enumType == some node.id && seed.fields.isNone && seed.backendRepresentation.isNone)
        "raw enum recipe retained a physical layout answer"
      compared := compared + 1
    else
      residuals := residuals + 1
      let missing ← must ((RuntimeMetadata.ofDocument { candidate with
        layouts := candidate.layouts.set! node.layoutId { seed with sizeBytes := none } }).mapError toString)
      check (!((RuntimeMetadata.layoutInWorld missing node.id).run world).isOk)
        "missing residual enum layout silently succeeded"
      check adt.args.isEmpty "residual fixture unexpectedly requires generic substitution"
      let constructedWorld ← must (TypeArena.World.ofMaterial #[] #[] candidate.definitions
        #[] metadata.target.pointerSize.bytes.toNat)
      let (constructedId,constructedWorld) ← must ((TypeArena.World.internType
        (.adt identity #[])).run constructedWorld)
      check (!((RuntimeMetadata.layoutInWorld sourceOnly constructedId).run constructedWorld).isOk)
        s!"constructed unsupported enum borrowed a physical material type ID: {node.display}"
    if #["DynamicControl","NestedDynamicControl"].contains node.display then
      check seed.enumType.isSome "covered dynamic enum retained a material layout answer"
      let constructedWorld ← must (TypeArena.World.ofMaterial #[] #[] candidate.definitions
        #[] metadata.target.pointerSize.bytes.toNat)
      let (constructedId,constructedWorld) ← must ((TypeArena.World.internType
        (.adt identity #[])).run constructedWorld)
      let (actual,finalWorld) ← must ((RuntimeMetadata.layoutInWorld sourceOnly constructedId).run constructedWorld)
      sourceDynamic := sourceDynamic + 1
      check (actual.layout == expected) s!"novel dynamic-field enum differs from pinned compiler: {node.display}\nEXPECTED {repr expected}\nACTUAL {repr actual.layout}"
      check (finalWorld.materialTypes.isEmpty && finalWorld.materialConstants.isEmpty && finalWorld.materialPredicates.isEmpty)
        "novel dynamic-field enum acquired a material result/source pool"
      let withoutConstructor := candidate.definitions.map fun declaration =>
        if declaration.adtDeclaration.any (·.langItem == some "dyn_metadata") then
          {declaration with adtDeclaration := none}
        else declaration
      let missingWorld ← must (TypeArena.World.ofMaterial #[] #[] withoutConstructor #[]
        metadata.target.pointerSize.bytes.toNat)
      let (missingId,missingWorld) ← must ((TypeArena.World.internType
        (.adt identity #[])).run missingWorld)
      check (!((RuntimeMetadata.layoutInWorld sourceOnly missingId).run missingWorld).isOk)
        "missing raw DynMetadata declaration produced a layout"
      let wrongHeader := candidate.definitions.map fun declaration =>
        if declaration.adtDeclaration.any (·.langItem == some "dyn_metadata") then
          {declaration with genericTemplate := declaration.genericTemplate.map fun template =>
            {template with parameters := #[.region]}}
        else declaration
      let malformedWorld ← must (TypeArena.World.ofMaterial #[] #[] wrongHeader #[]
        metadata.target.pointerSize.bytes.toNat)
      let (malformedId,malformedWorld) ← must ((TypeArena.World.internType
        (.adt identity #[])).run malformedWorld)
      check (!((RuntimeMetadata.layoutInWorld sourceOnly malformedId).run malformedWorld).isOk)
        "malformed raw DynMetadata generic header produced a layout"
  check (sourceDynamic == 2) "missing novel fat dynamic enum coverage"
  check (compared == 16 && residuals == 1) "missing enum source/residual coverage"
  let mut pointers := 0
  for node in candidate.types do
    unless (match node.shape with | .rawPointer .. | .reference .. => true | _ => false) do continue
    let pointee := match node.shape with
      | .rawPointer pointee _ | .reference pointee .. => pointee
      | _ => node.id
    let (tail,_) ← must ((RuntimeMetadata.metadataTailInWorld metadata pointee).run world)
    unless (← must (world.shapeKind tail)) == .dynamicTraitObject do continue
    let key ← must (GenericInstantiationWorld.ofType world 16384 node.id)
    let matching ← oracle.types.filterM fun old => do
      pure ((← must (GenericInstantiationWorld.ofType oracleWorld 16384 old.id)) == key)
    let some expectedNode := matching[0]? | throw (IO.userError "fat pointer compiler oracle absent")
    let empty ← must (TypeArena.World.ofMaterial #[] #[] candidate.definitions #[]
      metadata.target.pointerSize.bytes.toNat)
    let (fresh,empty) ← must ((GenericInstantiationWorld.resolveType 16384 key).run empty)
    let (actual,empty) ← must ((RuntimeMetadata.layoutInWorld sourceOnly fresh).run empty)
    check (actual.layout == (← oracle.layout expectedNode))
      s!"complete novel fat pointer differs from compiler: {node.display}"
    let freshPointee ← match ← must (empty.lookupType fresh) with
      | .constructed (.rawPointer pointee _) | .constructed (.reference pointee ..) => pure pointee
      | _ => throw (IO.userError "novel fat pointer constructor absent")
    let (metadataId,empty) ← must ((RuntimeMetadata.pointerMetadataTypeInWorld metadata freshPointee).run empty)
    let metadataKey ← must (GenericInstantiationWorld.ofType empty 16384 metadataId)
    let matchingMetadata ← oracle.types.filterM fun old => do
      pure ((← must (GenericInstantiationWorld.ofType oracleWorld 16384 old.id)) == metadataKey)
    let some expectedMetadata := matchingMetadata[0]? | throw (IO.userError "DynMetadata compiler oracle absent")
    let (metadataLayout,empty) ← must ((RuntimeMetadata.layoutInWorld sourceOnly metadataId).run empty)
    check (metadataLayout.layout == (← oracle.layout expectedMetadata))
      "complete novel DynMetadata ADT layout differs from compiler"
    check (empty.materialTypes.isEmpty && empty.materialConstants.isEmpty && empty.materialPredicates.isEmpty)
      "novel fat pointer acquired a material prefix"
    pointers := pointers + 1
  check (pointers >= 1) "fat pointer compiler coverage absent"
  let base := (← must (decodeJson (← IO.FS.readFile basePath))).document
  let baseMetadata ← must ((RuntimeMetadata.ofDocument base).mapError toString)
  let mut novel ← must (TypeArena.World.ofMaterial #[] #[] base.definitions
    #[] baseMetadata.target.pointerSize.bytes.toNat)
  let some expectedNode := oracle.types.find? (fun node => match node.shape with
    | .adt adt => adt.args.any fun arg => match arg with
      | .Type id => (oracle.types[id]?).any fun element => match element.shape with
        | .array _ _ constructor => constructor.count == 1031
        | _ => false
      | _ => false
    | _ => false) | throw (IO.userError "novel generic enum oracle absent")
  let .adt expectedAdt := expectedNode.shape | throw (IO.userError "novel oracle is not ADT")
  let identity ← must (oracleWorld.identity expectedAdt.definition)
  let (enumId,after) ← internNovelEnum identity novel
  novel := after
  let (actual,_) ← must ((RuntimeMetadata.layoutInWorld baseMetadata enumId).run novel)
  check (novel.materialTypes.isEmpty && novel.materialConstants.isEmpty)
    "novel enum control accidentally borrowed a material type/constant"
  check (actual.layout == (← oracle.layout expectedNode)) "novel generic enum layout differs from compiler"
  let missingDefinitions := base.definitions.map fun declaration =>
    if declaration.crateIndex == identity.crateIndex && declaration.index == identity.index then
      { declaration with adtDeclaration := none }
    else declaration
  let missingWorld ← must (TypeArena.World.ofMaterial #[] #[] missingDefinitions
    #[] baseMetadata.target.pointerSize.bytes.toNat)
  let (missingId,missingWorld) ← internNovelEnum identity missingWorld
  check (!((RuntimeMetadata.layoutInWorld baseMetadata missingId).run missingWorld).isOk)
    "missing raw enum declaration borrowed a material layout"
  for malformed in ["{\"enum_type\":0,\"struct_type\":0}",
      "{\"enum_type\":0,\"size_bytes\":0}", "{\"enum_type\":-1}"] do
    check (!(JsonReader.run DecoderValues.parseLayout malformed).isOk) "malformed enum recipe accepted"
  IO.println s!"PASS {pointers} complete novel fat pointer and DynMetadata ADT layouts; {sourceDynamic} complete novel fat dynamic enum layouts with empty type/constant/predicate prefixes and empty layout catalogue; missing/malformed DynMetadata source rejects; {compared} raw enum comparisons and novel generic enum regression"
