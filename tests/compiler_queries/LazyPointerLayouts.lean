import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

open Lean Miri.Input
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

private structure Oracle where
  target : Miri.ABI.RuntimeTargetDataLayout
  rows : Array Json
  layouts : Array Layout

/-- Only pointer constructors and raw physical layouts are read from the old
oracle. In particular, no missing alias rigidity or FnDef binder is guessed. -/
private def baselineMaterial (path : String) : IO Oracle := do
  let raw ← must (Json.parse (← IO.FS.readFile path))
  check ((← must ((← must (raw.getObjVal? "schema_version")).getNat?)) == 12)
    "expected canonical-main schema12 baseline"
  let targetInput ← must (JsonReader.run CatalogDecoder.targetDataLayout
    (← must (raw.getObjVal? "runtime_target_data_layout")).compress)
  let target ← must ((RuntimeMetadata.importTarget targetInput).mapError toString)
  let rows ← must ((← must (raw.getObjVal? "types")).getArr?)
  let values ← must ((← must (raw.getObjVal? "layout_values")).getArr?)
  let refs ← must ((← must (raw.getObjVal? "layouts")).getArr?)
  let layouts ← refs.mapM fun row => do
    let id ← must row.getNat?
    let some value := values[id]? | throw (IO.userError "baseline layout reference absent")
    must (JsonReader.run DecoderValues.parseLayout value.compress)
  pure ⟨target,rows,layouts⟩

private def Oracle.layout (oracle : Oracle) (id : Nat) : IO Miri.ABI.LayoutData := do
  let some row := oracle.rows[id]? | throw (IO.userError "baseline type absent")
  let layoutId ← must ((← must (row.getObjVal? "layout")).getNat?)
  let some layout := oracle.layouts[layoutId]? | throw (IO.userError "baseline layout absent")
  must ((RuntimeMetadata.layout oracle.target layout).mapError toString)

private def pointerNode? (row : Json) : IO (Option TypeNode) := do
  let shape ← must (row.getObjVal? "shape")
  let kind ← must ((← must (shape.getObjVal? "kind")).getStr?)
  unless ["raw_pointer","reference"].contains kind do return none
  let fields ← must row.getObj?
  let core := Json.mkObj (fields.toList.filter (·.1 != "compiler_facts"))
  return some (← must (JsonReader.run DecoderValues.parseTypeNode core.compress))

private def pointee (node : TypeNode) : IO (Nat × Bool) :=
  match node.shape with
  | .rawPointer child _ => pure (child,false)
  | .reference child .. => pure (child,true)
  | _ => throw (IO.userError "pointer constructor expected")

def main (args : List String) : IO Unit := do
  let [baselinePath,candidatePath] := args | throw (IO.userError "expected baseline12.json candidate13.json")
  let oracle ← baselineMaterial baselinePath
  let mut baselinePointers : Array TypeNode := #[]
  for row in oracle.rows do
    if let some node ← pointerNode? row then baselinePointers := baselinePointers.push node
  let mut direct := 0
  let mut covered : Array (String × Bool) := #[]
  -- This independently tests the physical pointer calculator using only rustc
  -- metadata dependencies, including dynamic metadata. It does not claim that
  -- the metadata-type query itself has been independently reconstructed here.
  for original in baselinePointers do
    let (child,isReference) ← pointee original
    let childLayout ← oracle.layout child
    let metadata ← if childLayout.isSized then pure none else do
      let some source := oracle.rows[child]? | throw (IO.userError "baseline pointee absent")
      let facts ← must (source.getObjVal? "compiler_facts")
      let queries ← must (facts.getObjVal? "type_queries")
      let id ← must ((← must (queries.getObjVal? "pointer_metadata_type")).getNat?)
      pure (some (← oracle.layout id))
    let actual ← must (Miri.ABI.PrimitiveLayout.pointer oracle.target isReference metadata)
    check (actual == (← oracle.layout original.id)) s!"pointer calculator differs from pinned rustc: {original.display}"
    let some source := oracle.rows[child]? | throw (IO.userError "baseline pointee absent")
    let rawKind ← must ((← must ((← must (source.getObjVal? "shape")).getObjVal? "kind")).getStr?)
    let kind := if childLayout.isSized then "sized" else match rawKind with
      | "str" => "str" | "slice" => "slice" | "dynamic_trait_object" => "dyn" | _ => "other"
    let coverage := (kind,isReference)
    unless covered.contains coverage do covered := covered.push coverage
    direct := direct + 1
  for kind in ["sized","str","slice","dyn"] do
    for reference in [false,true] do
      check (covered.contains (kind,reference)) s!"missing independent pointer coverage {kind}/ref={reference}"
  IO.println s!"PASS {direct} independent complete pointer/reference calculator layouts equal pinned rustc"
  let decoded ← must (decodeJson (← IO.FS.readFile candidatePath))
  let runtime ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  check (runtime.target == oracle.target) "comparison target differs from baseline"
  let some checked := runtime.checkedMaterial | throw (IO.userError "checked material prefix absent")
  let initial := TypeArena.World.ofCheckedMaterial checked
  let mut reused := 0
  for node in decoded.document.types do
    unless [.rawPointer,.reference].contains node.shapeKind do continue
    let some key ← must (initial.materialKey node) | throw (IO.userError "material pointer identity absent")
    let (id,afterIntern) ← must ((TypeArena.World.internType key).run initial)
    check (id == node.id && afterIntern.constructedTypes.isEmpty && afterIntern.constructedConstants.isEmpty)
      "canonical source constructor was duplicated instead of reused"
    let (actual,afterLayout) ← must ((runtime.layoutInWorld id).run afterIntern)
    check (afterLayout.constructedTypes.isEmpty && afterLayout.constructedConstants.isEmpty)
      "material pointer layout unexpectedly created execution syntax"
    let mut matched := false
    for prior in baselinePointers do
      -- Fixed-fixture spellings select the independent oracle only; runtime
      -- identities above are complete raw constructor keys, never spellings.
      if prior.display == node.display && prior.shapeKind == node.shapeKind then
        check (actual.layout == (← oracle.layout prior.id)) s!"source pointer layout differs from pinned rustc: {node.display}"
        matched := true
    check matched s!"source pointer lacks independent fixture correspondence: {node.display}"
    reused := reused + 1
  check (reused > 0) "no source pointer identities checked"
  IO.println s!"PASS {reused} canonical material pointer identities reused without duplicate IDs; source layouts equal independent rustc"
  IO.println "New absent-constructor algorithm evidence is separately checked by WorldLayouts.lean, including new ADT pointees and both wide-pointer fields."
