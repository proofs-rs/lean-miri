import Miri.Input.Decoder
import Miri.Input.WorldTypeHash

/-! The expected TypeId values come from a fresh pinned compiler process.
Raw generic trees are also resolved in an empty type/constant prefix, so this
comparison cannot succeed by looking up exported type-result rows. -/
open Lean Miri.Input Miri.Input.TypeArena
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [sourcePath,oraclePath] := args | throw (IO.userError "expected fresh nominal source and compiler oracle")
  let source := (← must (decodeJson (← IO.FS.readFile sourcePath))).document
  let mut world ← must (World.ofDocument source)
  let mut novel ← must (World.ofMaterial #[] #[] source.definitions #[] world.pointerBytes)
  let oracle ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rows ← must ((← must (oracle.getObjVal? "types")).getArr?)
  let mut compared := 0
  let mut nominal := 0
  let mut arrays := 0
  for row in rows do
    let display ← must (row.getObjValAs? String "display")
    let term ← must (GenericMaterialCodec.readTerm 4096 (← must (row.getObjVal? "type")))
    let (id,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run world)
    world := next
    let some _ ← must (WorldTypeHash.sourceBytes world 4096 id) | continue
    if let .material node ← must (world.lookupType id) then
      if node.compilerFacts.any (fun facts => facts.typeIdHash.isSome) then
        throw (IO.userError s!"covered source retained an eager hash: {display}")
    let expectedText ← must (row.getObjValAs? String "hash")
    let some expected := expectedText.toNat? | throw (IO.userError "invalid compiler hash decimal")
    let actual ← must (WorldTypeHash.query world 4096 id)
    unless actual.toNat == expected do throw (IO.userError s!"nominal source hash differs from rustc: {display}")
    let (fresh,next) ← must ((GenericInstantiationWorld.resolveType 4096 term).run novel)
    novel := next
    unless novel.materialTypes.isEmpty && novel.materialConstants.isEmpty do
      throw (IO.userError "novel source hash acquired a material result prefix")
    unless (← must (WorldTypeHash.query novel 4096 fresh)).toNat == expected do
      throw (IO.userError s!"novel source hash differs from rustc: {display}")
    let constructor ← match ← must (world.lookupType id) with
      | .constructed constructor => pure (some constructor)
      | .material node => must (world.materialKey node)
    match constructor with
    | some (.adt ..) | some (.functionDefinition ..) => nominal := nominal + 1
    | some (.array ..) => arrays := arrays + 1
    | _ => pure ()
    compared := compared + 1
  unless nominal ≥ 12 && arrays ≥ 1 do
    throw (IO.userError "nominal/array compiler differential coverage is incomplete")
  let some definition := source.definitions.find? (fun definition =>
    definition.adtDeclaration.any (fun declaration => !declaration.fields.isEmpty) &&
    definition.genericTemplate.any (fun template => template.parameters.isEmpty))
    | throw (IO.userError "field-bearing raw ADT declaration absent")
  let identity : GenericSubstitution.DefinitionIdentity := ⟨definition.crateIndex, definition.index⟩
  let definitions := source.definitions.map fun current =>
    if current.crateIndex == identity.crateIndex && current.index == identity.index then
      {current with adtDeclaration := none} else current
  let broken ← must (World.ofMaterial #[] #[] definitions #[] world.pointerBytes)
  let (id,broken) ← must ((World.internType (.adt identity #[])).run broken)
  if (WorldTypeHash.query broken 4096 id).isOk then
    throw (IO.userError "missing raw ADT declaration was accepted")
  let some declaration := definition.adtDeclaration | throw (IO.userError "raw ADT declaration absent")
  let some field := declaration.fields[0]? | throw (IO.userError "raw ADT field absent")
  let missingPath := source.definitions.map fun current =>
    if current.crateIndex == field.definition.crateIndex && current.index == field.definition.index then
      {current with rawPath := none} else current
  let broken ← must (World.ofMaterial #[] #[] missingPath #[] world.pointerBytes)
  let (id,broken) ← must ((World.internType (.adt identity #[])).run broken)
  if (WorldTypeHash.query broken 4096 id).isOk then
    throw (IO.userError "missing raw field definition path was accepted")
  let malformed := source.definitions.map fun current =>
    if current.crateIndex == identity.crateIndex && current.index == identity.index then
      {current with adtDeclaration := some {declaration with flagsBits := 2^15}} else current
  match World.ofMaterial #[] #[] malformed #[] world.pointerBytes with
  | .error _ => pure ()
  | .ok broken =>
    let (id,broken) ← must ((World.internType (.adt identity #[])).run broken)
    if (WorldTypeHash.query broken 4096 id).isOk then
      throw (IO.userError "unknown raw ADT flags were accepted")
  IO.println s!"PASS {compared} fresh raw type hashes ({nominal} nominal, {arrays} arrays), empty-prefix construction and missing-declaration/path/flags controls"
