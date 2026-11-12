import Miri.ABI.UnivariantLayout
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

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected pinned baseline export")
  let source ← readFixture path 12
  let mut count := 0
  for node in source.types do
    let .tuple elements := node.shape | continue
    let fields ← elements.mapM source.lookup
    let expected ← source.lookup node.id
    let kind := if elements.isEmpty then Miri.ABI.UnivariantLayout.Kind.alwaysSized
      else .maybeUnsized
    let actual ← must (Miri.ABI.UnivariantLayout.compute source.target fields {} kind)
    check (actual == expected) s!"tuple univariant mismatch: {node.id}\nexpected={repr expected}\nactual={repr actual}"
    count := count + 1
  let mut structs := 0
  -- These named fixture declarations have no generic or unsized tail fields;
  -- their source caller selects AlwaysSized. This finite adapter is not a
  -- general inference of definition-level sizedness from instantiated fields.
  for node in source.types do
    unless ["C", "Packed", "Aligned", "Transparent", "Reordered", "ScalarPair", "Empty"].contains node.display do continue
    let .adt data := node.shape | throw (IO.userError "fixture struct shape mismatch")
    let some variant := data.variants[0]? | throw (IO.userError "fixture struct variant missing")
    let fields ← variant.fields.mapM (fun field => source.lookup field.typeId)
    let rawRepr := data.representation
    let representation : Miri.ABI.UnivariantLayout.Representation := {
      flags := UInt8.ofNat rawRepr.flagsBits, integerRepresentation := rawRepr.integer.isSome,
      align := ← rawRepr.alignBytes.mapM (fun bytes => must ((RuntimeMetadata.alignment bytes).mapError toString)),
      pack := ← rawRepr.packBytes.mapM (fun bytes => must ((RuntimeMetadata.alignment bytes).mapError toString)),
      fieldShuffleSeed := UInt64.ofNat rawRepr.fieldShuffleSeed }
    let actual ← must (Miri.ABI.UnivariantLayout.compute source.target fields representation .alwaysSized)
    let expected ← source.lookup node.id
    check (actual == expected) s!"struct univariant mismatch: {node.display}\nexpected={repr expected}\nactual={repr actual}"
    structs := structs + 1
  check (structs == 7) s!"fixture struct coverage incomplete: {structs}"
  check (count >= 1) "no tuple source oracle"
  IO.println s!"PASS {structs} complete struct layouts equal pinned rustc (C, packed, aligned, transparent, reordered, scalar pair, empty)"
  IO.println s!"PASS {count} complete tuple layouts equal pinned rustc"
