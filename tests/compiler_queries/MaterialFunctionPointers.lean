import Miri.Input.Decoder
import Miri.Input.WorldNormalization
import Miri.Input.RuntimeMetadata

open Lean Miri.Input Miri.Input.TypeArena
private def must {α} [ToString ε] : Except ε α → IO α
  | .ok value => pure value | .error error => throw (IO.userError (toString error))

/-- The baseline is an immutable eager exporter of the same source and compiler.
Only its physical layout rows are decoded here; no old input contract is added
back to the production decoder. -/
private def baselineLayout (raw : Json) (target : Miri.ABI.RuntimeTargetDataLayout)
    (name : String) : IO Miri.ABI.LayoutData := do
  let rows ← must ((← must (raw.getObjVal? "types")).getArr?)
  let rows ← rows.filterM fun row => do
    pure ((← must ((← must (row.getObjVal? "display")).getStr?)) == name)
  unless rows.size == 1 do throw (IO.userError "baseline layout type key is ambiguous/absent")
  let some row := rows[0]? | throw (IO.userError "baseline type absent")
  let layoutId ← must ((← must (row.getObjVal? "layout")).getNat?)
  let values ← must ((← must (raw.getObjVal? "layout_values")).getArr?)
  let refs ← must ((← must (raw.getObjVal? "layouts")).getArr?)
  let layouts ← refs.mapM fun reference => do
    let reference ← must reference.getNat?
    let some value := values[reference]? | throw (IO.userError "baseline layout reference absent")
    must (JsonReader.run DecoderValues.parseLayout value.compress)
  must ((RuntimeMetadata.resolveLayout target #[] layouts layoutId #[] #[] #[]).mapError toString)

def main (args : List String) : IO Unit := do
  let [candidatePath,baseWorldPath,baselinePath] := args
    | throw (IO.userError "expected fresh candidate, separate base world and eager baseline")
  let candidate := (← must (decodeJson (← IO.FS.readFile candidatePath))).document
  let base := (← must (decodeJson (← IO.FS.readFile baseWorldPath))).document
  let baseline ← must (Json.parse (← IO.FS.readFile baselinePath))
  -- Remove every normalization answer for the material FnPtr domain. The test
  -- must succeed from its raw constructor/header instead of a residual row.
  let types := candidate.types.map fun node => match node.shape with
    | .functionPointer .. => {node with compilerFacts := node.compilerFacts.map fun facts =>
        {facts with typeQueries := facts.typeQueries.filter (·.1 != "normalized")} }
    | _ => node
  let candidate := {candidate with types}
  let metadata ← must ((RuntimeMetadata.ofDocument candidate).mapError toString)
  let baseMetadata ← must ((RuntimeMetadata.ofDocument base).mapError toString)
  let mut world ← must (World.ofDocument candidate)
  let mut fresh ← must (World.ofDocument base)
  let some rawTarget := candidate.runtimeTargetDataLayout | throw (IO.userError "raw target absent")
  let target ← must ((RuntimeMetadata.importTarget rawTarget).mapError toString)
  let mut checked := 0
  for node in candidate.types do
    let .functionPointer _ variables := node.shape | continue
    unless variables.isEmpty do throw (IO.userError "fixture unexpectedly has a binder")
    let some key ← must (world.materialKey node) | throw (IO.userError "fresh FnPtr raw header absent")
    let (interned,next) ← must ((World.internType key).run world)
    unless interned == node.id && next.typeCount == world.typeCount do
      throw (IO.userError "complete material FnPtr did not reuse its exact canonical identity")
    world := next
    let (normalized,next) ← must ((WorldNormalization.normalizeType metadata.normalizationContext 10000 512 node.id).run world)
    unless normalized == node.id do throw (IO.userError "material FnPtr normalization changed identity")
    world := next
    let term ← must (GenericInstantiationWorld.ofType world 512 node.id)
    let (novel,next) ← must ((GenericInstantiationWorld.resolveType 512 term).run fresh)
    fresh := next
    unless novel >= fresh.materialTypes.size do throw (IO.userError "separate world eagerly contained FnPtr")
    let (actual,next) ← must ((RuntimeMetadata.layoutInWorld baseMetadata novel).run fresh)
    fresh := next
    let expected ← baselineLayout baseline target node.display
    unless actual.layout == expected do throw (IO.userError s!"complete constructed FnPtr layout differs: {node.display}")
    checked := checked + 1
  unless checked >= 6 do throw (IO.userError "fixture lacks six FnPtr signatures")
  IO.println s!"PASS {checked} fresh material canonical identities and normalization without result rows; complete constructed layouts match pinned eager baseline"
