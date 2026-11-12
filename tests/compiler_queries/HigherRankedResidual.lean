import Miri.Input.Decoder
import Miri.Input.WorldNormalization

open Miri.Input Miri.Input.TypeArena
private def must (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected actual unsupported-child HRTB source")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let metadata ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let world ← must (World.ofDocument document)
  let mut checked := 0
  for node in document.types do
    let .functionPointer _ variables := node.shape | continue
    if variables.isEmpty then continue
    let some (.functionPointer signature) ← must (world.materialKey node) | continue
    if ← must (GenericInstantiationWorld.supportsTypeReification world 4096 node.id) then continue
    let some facts := node.compilerFacts | throw (IO.userError "residual source facts absent")
    let some (_,some expected) := facts.typeQueries.find? (·.1 == "normalized")
      | throw (IO.userError "actual compiler normalization answer absent")
    let (actual,after) ← must ((WorldNormalization.normalizeType metadata.normalizationContext 10000 4096 node.id).run world)
    unless actual == expected && after.constructedTypes.isEmpty do
      throw (IO.userError "unsupported material child lost its exact compiler residual")
    let missing := document.types.map fun source =>
      if source.id == node.id then {source with compilerFacts := source.compilerFacts.map fun facts =>
        {facts with typeQueries := facts.typeQueries.filter (·.1 != "normalized")}}
      else source
    let absent ← must (World.ofMaterial missing document.typeConstants document.definitions world.pointerBytes)
    if ((WorldNormalization.normalizeType metadata.normalizationContext 10000 4096 node.id).run absent).isOk then
      throw (IO.userError "missing residual normalization answer was invented")
    let some child := signature.inputs[0]? | throw (IO.userError "dynamic signature input absent")
    let (novel,novelWorld) ← must ((World.internType
      (.functionPointer {signature with inputs := #[child,child]})).run world)
    unless novel >= world.materialTypes.size do throw (IO.userError "constructed residual control reused material")
    if ((WorldNormalization.normalizeType metadata.normalizationContext 10000 4096 novel).run novelWorld).isOk then
      throw (IO.userError "constructed unsupported child borrowed a material normalization answer")
    checked := checked + 1
  unless checked > 0 do throw (IO.userError "no actual HRTB residual boundary was exercised")
  IO.println s!"PASS {checked} actual HRTB material residuals; missing answers and constructed collisions reject"
