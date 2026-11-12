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
  let types ← typeRows.mapM fun row => do
    let fields ← must row.getObj?
    let row := Json.mkObj (fields.toList.filter (fun field => field.1 != "compiler_facts"))
    must (JsonReader.run DecoderValues.parseTypeNode row.compress)
  let values ← must ((← must (raw.getObjVal? "layout_values")).getArr?)
  let refs ← must ((← must (raw.getObjVal? "layouts")).getArr?)
  let layouts ← refs.mapM fun row => do
    let id ← must row.getNat?
    let some value := values[id]? | throw (IO.userError "layout value reference absent")
    must (JsonReader.run DecoderValues.parseLayout value.compress)
  return ⟨target,types,layouts⟩

private def Fixture.lookup (fixture : Fixture) (id : Nat) : IO Miri.ABI.LayoutData := do
  let some node := fixture.types.find? (·.id == id) | throw (IO.userError "type absent")
  let some layout := fixture.layouts[node.layoutId]? | throw (IO.userError "layout absent")
  must ((RuntimeMetadata.layout fixture.target layout).mapError toString)

/-- Compare complete computed layouts to rustc's eager layouts from a separate
baseline export of exactly the same fixture/compiler/flags. -/
def main (args : List String) : IO Unit := do
  for invalid in ["{\"primitive_recipe\":\"imaginary\"}",
      "{\"primitive_recipe\":\"bool\",\"size_bytes\":1}",
      "{\"primitive_recipe\":\"bool\",\"backend_repr\":null}"] do
    check (match JsonReader.run DecoderValues.parseLayout invalid with
      | .error _ => true | .ok _ => false)
      s!"accepted malformed primitive layout recipe {invalid}"
  let [baselinePath,candidatePath] := args
    | throw (IO.userError "expected baseline-export.json candidate-export.json")
  let baseline ← readFixture baselinePath 12
  let candidate ← readFixture candidatePath 13
  check (baseline.target == candidate.target) "comparison target layouts differ"
  let mut count := 0
  for node in candidate.types do
    let some input := candidate.layouts[node.layoutId]?
      | throw (IO.userError "candidate layout missing")
    let some recipe := input.primitiveRecipe | continue
    let matching := baseline.types.filter (fun prior => prior.shapeKind == node.shapeKind && prior.shapeMetadata == node.shapeMetadata)
    check (!matching.isEmpty) s!"primitive {recipe} lacks a baseline type"
    let some prior := matching[0]? | throw (IO.userError "baseline invariant")
    let expected ← baseline.lookup prior.id
    -- Function pointer signatures have one uniform scalar layout. Verify all
    -- matching baseline signatures, rather than using their local type IDs.
    for another in matching do
      let value ← baseline.lookup another.id
      check (value == expected) s!"nonuniform baseline primitive family {recipe}"
    let actual ← candidate.lookup node.id
    check (expected == actual) s!"primitive layout differs from rustc: {recipe}\nexpected={repr expected}\nactual={repr actual}"
    check (input.sizeBytes.isNone && input.abiAlignBytes.isNone &&
      input.backendRepresentation.isNone && input.fields.isNone)
      s!"primitive {recipe} retained eager layout result"
    count := count + 1
  check (count >= 21) s!"primitive fixture coverage incomplete: {count}"
  let mut arrays := 0
  for node in baseline.types do
    let .array element _ constructor := node.shape | continue
    let elem ← baseline.lookup element
    let expected ← baseline.lookup node.id
    check (constructor.count < 2^64) "oracle array count exceeds u64"
    let actual ← must (Miri.ABI.PrimitiveLayout.arrayLike baseline.target elem
      (UInt64.ofNat constructor.count))
    check (expected == actual) s!"array layout differs from rustc: element={element}, count={constructor.count}"
    arrays := arrays + 1
  check (arrays >= 4) s!"array fixture coverage incomplete: {arrays}"
  let byte ← must (Miri.ABI.PrimitiveLayout.compute candidate.target "u8")
  let overflow := Miri.ABI.PrimitiveLayout.arrayLike candidate.target byte
    candidate.target.base.objSizeBound
  check (match overflow with | .error _ => true | .ok _ => false)
    "array accepted exclusive object-size bound"
  let oneLess ← must (Miri.ABI.PrimitiveLayout.arrayLike candidate.target byte
    (candidate.target.base.objSizeBound - 1))
  check (oneLess.size.bytes == candidate.target.base.objSizeBound - 1)
    "array rejected size below exclusive object-size bound"
  IO.println s!"PASS {arrays} complete array layouts equal pinned rustc; zero/nonzero lengths, ZST elements and exclusive target bound"
  IO.println s!"PASS {count} complete primitive layouts equal pinned rustc; size, alignment, scalar ranges, niches, variants and randomization seeds"
