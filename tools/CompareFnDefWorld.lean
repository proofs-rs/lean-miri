import Miri.Input.TableTail
import Miri.Input.TypeConstCodec
import Miri.Input.CatalogDecoderRuntime
import Miri.Input.GenericMaterialCodec
import Miri.Input.GenericInstantiationWorld

/-! Fresh actual rustc FnDef trees compared to the execution-owned interner.
All known source identities must be reused without allocating replacement IDs. -/
open Lean Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [inputPath,oraclePath] := args | throw (IO.userError "expected fresh input.json oracle.json")
  -- Decode exactly the source constructor category under comparison. Unrelated
  -- query catalogs/bodies are not supplied as hypothetical dependency material.
  let raw ← must (Json.parse (← IO.FS.readFile inputPath))
  unless (← must ((← must (raw.getObjVal? "schema_version")).getNat?)) == 13 do
    throw (IO.userError "FnDef World reader requires current source schema13")
  let definitions ← (← must ((← must (raw.getObjVal? "definitions")).getArr?)).mapM fun row =>
    must (JsonReader.run (DecoderValues.parseDefinitionId "$oracle.definition") row.compress)
  let types ← (← must ((← must (raw.getObjVal? "types")).getArr?)).mapM fun row =>
    do
      let fields ← must row.getObj?
      let source := Json.mkObj ((fields.toArray.filter (·.1 != "compiler_facts")).toList)
      must (JsonReader.run (DecoderValues.parseTypeNode "$oracle.type") source.compress)
  let constants ← (← must ((← must (raw.getObjVal? "type_constants")).getArr?)).mapM fun row =>
    must (JsonReader.run (TypeConstCodec.decode "$oracle.constant") row.compress)
  let target ← must (JsonReader.run CatalogDecoder.targetDataLayout
    (← must (raw.getObjVal? "runtime_target_data_layout")).compress)
  let initial ← must (TypeArena.World.ofMaterial types constants definitions
    target.defaultAddressSpacePointerSpec.pointerSizeBytes)
  let rows ← must ((← must (Json.parse (← IO.FS.readFile oraclePath))).getArr?)
  unless rows.size ≥ 3 do throw (IO.userError "FnDef World oracle requires three actual Rust callees")
  let mut world := initial
  let mut signatureBinders := 0
  for row in rows do
    let expected ← must (GenericMaterialCodec.readTerm 1024 (← must (row.getObjVal? "expected")))
    let (id,updated) ← must ((GenericInstantiationWorld.resolveType 1024 expected).run world)
    world := updated
    unless id < types.size && world.constructedTypes.isEmpty do
      throw (IO.userError "World failed to reuse exact material FnDef identity")
    unless (← must (GenericInstantiationWorld.ofType world 1024 id)) == expected do
      throw (IO.userError "World FnDef rustc/Lean constructor mismatch")
    let .material node ← must (world.lookupType id) | throw (IO.userError "material FnDef became constructed")
    let .functionDefinition _ _ _ signatureVariables argumentVariables := node.shape
      | throw (IO.userError "material FnDef became a different constructor")
    let signatureCount ← must ((← must (row.getObjVal? "signature_binders")).getNat?)
    let argumentCount ← must ((← must (row.getObjVal? "argument_binders")).getNat?)
    unless signatureCount == signatureVariables.size && argumentCount == argumentVariables.size do
      throw (IO.userError "World confused FnDef signature and argument binders")
    if signatureCount > 0 then signatureBinders := signatureBinders + 1
  unless signatureBinders > 0 do throw (IO.userError "World FnDef fixture lacks nonempty signature binder")
  IO.println s!"PASS {rows.size} fresh rustc/World FnDef identities with exact material reuse; nonempty_signature_binders={signatureBinders}"
