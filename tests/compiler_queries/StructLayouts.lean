import Miri.ABI.StructLayout
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
  return ⟨target,types,layouts⟩

private def Fixture.lookup (fixture : Fixture) (id : Nat) : IO Miri.ABI.LayoutData := do
  let some node := fixture.types.find? (·.id == id) | throw (IO.userError "type absent")
  must ((RuntimeMetadata.resolveLayout fixture.target fixture.types fixture.layouts node.layoutId).mapError toString)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected pinned struct baseline export")
  let source ← readFixture path 12
  let raw ← must (Json.parse (← IO.FS.readFile path))
  let rows ← must ((← must (raw.getObjVal? "types")).getArr?)
  let booleans ← must ((← must (raw.getObjVal? "boolean_queries")).getArr?)
  let mut count := 0
  for row in rows do
    let facts ← must (row.getObjVal? "compiler_facts")
    let boolId ← must ((← must (facts.getObjVal? "boolean_queries")).getNat?)
    let some flags := booleans[boolId]? | throw (IO.userError "boolean material pool absent")
    unless (← must ((← must (flags.getObjVal? "is_unsafe_cell")).getBool?)) do continue
    let id ← must ((← must (row.getObjVal? "type_id")).getNat?)
    let some node := source.types.find? (·.id == id) | throw (IO.userError "UnsafeCell source shape absent")
    let .adt data := node.shape | throw (IO.userError "UnsafeCell identity on non-ADT")
    let some variant := data.variants[0]? | throw (IO.userError "UnsafeCell variant absent")
    let fields ← variant.fields.mapM (fun field => source.lookup field.typeId)
    let rawRepr := data.representation
    let representation : Miri.ABI.UnivariantLayout.Representation := {
      flags := UInt8.ofNat rawRepr.flagsBits, integerRepresentation := rawRepr.integer.isSome,
      align := ← rawRepr.alignBytes.mapM (fun bytes => must ((RuntimeMetadata.alignment bytes).mapError toString)),
      pack := ← rawRepr.packBytes.mapM (fun bytes => must ((RuntimeMetadata.alignment bytes).mapError toString)),
      fieldShuffleSeed := UInt64.ofNat rawRepr.fieldShuffleSeed }
    -- Pinned library/core/src/cell.rs::UnsafeCell<T: ?Sized> caller adapter:
    -- UnsafeCell has a parameter
    -- tail in its declaration, so alwaysSized=false even when T is sized.
    -- Its lang-item identity above selects disabled niche optimization.
    let actual ← must (Miri.ABI.StructLayout.compute source.target fields representation 0 false false .disabled)
    let expected ← source.lookup id
    check (actual == expected) s!"UnsafeCell struct layout differs from pinned rustc: {node.display}\nexpected={repr expected}\nactual={repr actual}"
    check (actual.largestNiche.isNone) "UnsafeCell retained an outer niche"
    count := count + 1
  check (count >= 5) s!"UnsafeCell fixture coverage incomplete: {count}"
  IO.println s!"PASS {count} complete UnsafeCell layouts equal pinned rustc (scalar/pair/array/ZST/DST); source caller flags are explicit"
