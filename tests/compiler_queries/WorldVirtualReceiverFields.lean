import Miri.Input.Decoder
import Miri.Input.WorldInstanceAbi

open Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
def main (args : List String) : IO Unit := do
  let [path,oraclePath] := args | throw (IO.userError "expected raw field boundary source and independent field-layout oracle")
  let oracle ← match Lean.Json.parse (← IO.FS.readFile oraclePath) with
    | .ok value => pure value | .error error => throw (IO.userError error)
  let expected ← must do (← oracle.getObjVal? "fields").getArr?
  unless expected.size == 5 do throw (IO.userError "independent raw-field oracle count differs")
  let decoded := (← must (decodeJson (← IO.FS.readFile path))).document
  let poisonedTypes := decoded.types.map fun (node : TypeNode) =>
    let shape : TypeShape := match node.shape with
      | .adt data =>
        let variants := data.variants.map fun (variant : AdtVariant) =>
          {variant with fields := variant.fields.map (fun field => {field with typeId := decoded.queries.primitives.u8})}
        .adt {data with variants}
      | other => other
    let compilerFacts := node.compilerFacts.map (fun facts => {facts with booleanQueries := #[],projectionQueries := none,adt := none})
    {node with shape,compilerFacts}
  let document := {decoded with types := poisonedTypes}
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create metadata).mapError reprStr)
  let (definition,arguments) ← must do
    let mut found := none
    for node in document.instances do
      if let .Item definition := node.instanceKind then
        let name := ((document.definitions[definition]?.bind (·.rawPath)).bind (·.components.back?)).bind (·.name)
        if name == some "boundary" then
          if found.isSome then throw "duplicate raw root Item"
          found := some (definition,node.genericArgs)
    let some request := found | throw "raw boundary Item header absent"
    pure request
  let (raw,signatureWorld) ← must ((InstanceSignature.instantiateDefinition 16384 definition arguments).run initial)
  let signature ← must (WorldFunctionPointerAbi.erasedSourceSignature raw)
  let (inputs,inputWorld) ← must ((signature.inputs.mapM fun term => RuntimeArrayTypes.liftType
    (WorldNormalization.resolveNormalizedTerm metadata.normalizationContext 100000 16384 term)).run signatureWorld)
  unless inputs.size == 5 do throw (IO.userError "raw field boundary arity mismatch")
  let some session := document.producer.abiSession | throw (IO.userError "ABI session absent")
  let mut world := inputWorld
  for (id,index) in inputs.zipIdx do
    let (field,after) ← must ((RuntimeArrayTypes.liftType (RuntimeMetadata.fieldTypeInWorld metadata id 0 0)).run world)
    let (layout,after) ← must ((RuntimeArrayTypes.liftType (RuntimeMetadata.layoutInWorld metadata field)).run after)
    let oneZst := layout.layout.size.bytes == 0 && layout.layout.align.abi.pow2 == 0
    let some row := expected[index]? | throw (IO.userError "independent field row absent")
    let expectedIndex ← must do (← row.getObjVal? "index").getNat?
    let expectedOne ← must do (← row.getObjVal? "one_zst").getBool?
    let expectedSize ← must do (← row.getObjVal? "size_bytes").getNat?
    let expectedAlign ← must do (← row.getObjVal? "align_bytes").getNat?
    unless expectedIndex == index && oneZst == expectedOne &&
        layout.layout.size.bytes.toNat == expectedSize && 2^layout.layout.align.abi.pow2 == expectedAlign do
      throw (IO.userError s!"raw source field layout differs from independent rustc oracle case{index}")
    match (WorldVirtualAbi.receiver session id).run after with
    | .error error =>
      if index == 2 then throw (IO.userError s!"raw transparent pointer receiver rejected: {error}")
      world := after
    | .ok (actual,updated) =>
      unless index == 2 do throw (IO.userError s!"out-of-domain source receiver accepted case{index}")
      let .Direct attributes := actual.mode | throw (IO.userError "raw wrapper receiver not direct")
      unless attributes.regular == 128 do throw (IO.userError "raw wrapper borrowed attributes fabricated")
      let _ ← must (updated.arena.lookupType actual.layout.ty)
      unless updated.arena.typeCount >= after.arena.typeCount do throw (IO.userError "source query lost appended type identities")
      world := updated
  IO.println "PASS5 source raw-field computed one-ZST vs source gate boundaries;successful append-only receiver World retained"
