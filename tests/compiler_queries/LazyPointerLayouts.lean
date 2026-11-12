import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

open Lean Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

/-- Source-derived comparison adapter: retain baseline rustc layouts and exact
pointer-metadata dependency IDs. No candidate query result serves as oracle.
Unrelated baseline catalogs are not decoded as candidate-schema data. -/
private def baselineMaterial (path : String) :
    IO (Miri.ABI.RuntimeTargetDataLayout × Array TypeNode × Array Layout) := do
  let raw ← must (Json.parse (← IO.FS.readFile path))
  check ((← must ((← must (raw.getObjVal? "schema_version")).getNat?)) == 12)
    "expected canonical-main schema12 baseline"
  let targetJson ← must (raw.getObjVal? "runtime_target_data_layout")
  let targetInput ← must (JsonReader.run CatalogDecoder.targetDataLayout targetJson.compress)
  let target ← must ((RuntimeMetadata.importTarget targetInput).mapError toString)
  let rows ← must ((← must (raw.getObjVal? "types")).getArr?)
  let types ← rows.mapM fun row => do
    let fields ← must row.getObj?
    let core := Json.mkObj (fields.toList.filter (fun field => field.1 != "compiler_facts"))
    let node ← must (JsonReader.run DecoderValues.parseTypeNode core.compress)
    let facts ← must (row.getObjVal? "compiler_facts")
    let queryObject ← must ((← must (facts.getObjVal? "type_queries")).getObj?)
    let queries ← queryObject.toList.toArray.mapM fun (key,value) => do
      if value == Json.null then pure (key, none)
      else pure (key, some (← must value.getNat?))
    return {node with compilerFacts := some {
      typingEnvironment := "fully_monomorphized", booleanQueries := #[], typeQueries := queries}}
  let values ← must ((← must (raw.getObjVal? "layout_values")).getArr?)
  let refs ← must ((← must (raw.getObjVal? "layouts")).getArr?)
  let layouts ← refs.mapM fun row => do
    let id ← must row.getNat?
    let some value := values[id]? | throw (IO.userError "baseline layout reference absent")
    must (JsonReader.run DecoderValues.parseLayout value.compress)
  pure (target, types, layouts)

def main (args : List String) : IO Unit := do
  let [baselinePath, candidatePath] := args
    | throw (IO.userError "expected baseline12.json candidate13.json")
  let (target, types, layouts) ← baselineMaterial baselinePath
  -- The direct source algorithm comparison runs independently of candidate
  -- MIR decoding, followed below by the integrated synthetic-ID comparison.
  let baselineLayout (id : Nat) : IO Miri.ABI.LayoutData := do
    let some source := types[id]? | throw (IO.userError "baseline type absent")
    let some input := layouts[source.layoutId]? | throw (IO.userError "baseline layout absent")
    must ((RuntimeMetadata.layout target input).mapError toString)
  let mut direct := 0
  for original in types do
    let constructor := match original.shape with
      | .rawPointer child .Mut => some (child, false)
      | .reference child .Mut .Erased => some (child, true)
      | _ => none
    let some (child, isReference) := constructor | continue
    let childLayout ← baselineLayout child
    let pointerMetadata ← if childLayout.isSized then pure none else do
      let some childNode := types[child]? | throw (IO.userError "baseline pointee absent")
      let some facts := childNode.compilerFacts | throw (IO.userError "baseline pointee facts absent")
      let some (_,some id) := facts.typeQueries.find? (·.1 == "pointer_metadata_type")
        | throw (IO.userError "baseline metadata type absent")
      pure (some (← baselineLayout id))
    let actual ← must (Miri.ABI.PrimitiveLayout.pointer target isReference pointerMetadata)
    let expected ← baselineLayout original.id
    check (actual == expected) s!"direct pointer source algorithm differs from rustc: {original.display}"
    direct := direct + 1
  IO.println s!"PASS {direct} direct complete pointer/reference layouts equal pinned rustc"
  let decoded ← must (decodeJson (← IO.FS.readFile candidatePath))
  -- Baseline type/layout material alone determines the comparison. Candidate
  -- records supply unrelated required fields of the internal document structure.
  let runtime ← must ((RuntimeMetadata.ofDocument
    {decoded.document with types, layouts}).mapError toString)
  check (runtime.target == target) "comparison target differs from baseline"
  let mut count := 0
  let mut covered : Array (String × Bool) := #[]
  for original in types do
    let constructor := match original.shape with
      | .rawPointer child .Mut => some (child, false)
      | .reference child .Mut .Erased => some (child, true)
      | _ => none
    let some (pointee, isReference) := constructor | continue
    let some source := types[pointee]? | throw (IO.userError "baseline pointee absent")
    let some expectedInput := layouts[original.layoutId]?
      | throw (IO.userError "baseline pointer layout absent")
    let expected ← must ((RuntimeMetadata.layout target expectedInput).mapError toString)
    -- Force a recipe ID even when an equivalent material constructor exists.
    let forced := TypeArena.constructedId types.size pointee isReference
    check (forced >= types.size) "synthetic namespace overlaps material"
    let actual ← must ((runtime.lookup forced).mapError toString)
    check (actual.layout == expected)
      s!"lazy pointer layout differs from rustc: {original.display}\nexpected={repr expected}\nactual={repr actual.layout}"
    let kind := match source.shape with
      | .str => "str" | .slice _ => "slice" | .dynamicTraitObject .. => "dyn"
      | _ => "other"
    let pointeeLayout ← must ((runtime.lookup pointee).mapError toString)
    let kind := if pointeeLayout.layout.isSized then "sized" else kind
    let coverage := (kind,isReference)
    unless covered.contains coverage do covered := covered.push coverage
    count := count + 1
  for kind in ["sized", "str", "slice", "dyn"] do
    for isReference in [false, true] do
      check (covered.contains (kind,isReference)) s!"missing oracle coverage {kind}/ref={isReference}"
  IO.println s!"PASS {count} forced-lazy pointer/reference complete layouts equal pinned rustc, including sized,str,slice,dyn pointees"
