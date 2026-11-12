import Miri.ABI.EnumLayout
import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata

/-! Component comparison: historical compiler material supplies child layouts
and evaluated discriminants. This checks the calculator, including explicit
repr inputs; it does not establish source discriminant CTFE support. -/
open Lean Miri.Input Miri.ABI

private def must (value : Except String α) : IO α :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)

private structure Oracle where
  target : RuntimeTargetDataLayout
  types : Array TypeNode
  layouts : Array Miri.Input.Layout
  definitions : Array DefinitionId
  constants : Array Miri.MIR.TypeConst

/-- Focused historical producer adapter: read raw type identity and actual
layout records, not old executable/catalog protocols or ADT declaration schema.
Only physical definition identity is needed to compare these closed type keys. -/
private def readOracle (path : String) : IO Oracle := do
  let raw ← must (Json.parse (← IO.FS.readFile path))
  let target ← must (JsonReader.run CatalogDecoder.targetDataLayout
    (← must (raw.getObjVal? "runtime_target_data_layout")).compress)
  let target ← must ((RuntimeMetadata.importTarget target).mapError toString)
  let types ← (← must ((← must (raw.getObjVal? "types")).getArr?)).mapM fun row => do
    let fields ← must row.getObj?
    let row := Json.mkObj (fields.toList.filter (fun field => field.1 != "compiler_facts"))
    must (JsonReader.run DecoderValues.parseTypeNode row.compress)
  let definitions ← (← must ((← must (raw.getObjVal? "definitions")).getArr?)).mapM fun row => do
    pure ({
      crateIndex := ← must ((← must (row.getObjVal? "crate")).getNat?)
      index := ← must ((← must (row.getObjVal? "index")).getNat?) } : DefinitionId)
  let values ← must ((← must (raw.getObjVal? "layout_values")).getArr?)
  let layouts ← (← must ((← must (raw.getObjVal? "layouts")).getArr?)).mapM fun row => do
    let index ← must row.getNat?
    let some value := values[index]? | throw (IO.userError "oracle layout reference absent")
    must (JsonReader.run DecoderValues.parseLayout value.compress)
  let constants ← (← must ((← must (raw.getObjVal? "type_constants")).getArr?)).mapM fun row =>
    must (JsonReader.run (TypeConstCodec.decode "oracle.constant") row.compress)
  pure ⟨target,types,layouts,definitions,constants⟩

private def Oracle.layout (oracle : Oracle) (node : TypeNode) : IO LayoutData :=
  must ((RuntimeMetadata.resolveLayout oracle.target oracle.types oracle.layouts node.layoutId
    oracle.definitions oracle.constants).mapError toString)


private def integerFromRaw : ReprInteger → IO IntegerType
  | .pointerSized signed => pure (.Pointer signed)
  | .fixed _ bits signed => do
    let integer ← match bits with
      | 8 => pure Integer.I8 | 16 => pure .I16 | 32 => pure .I32
      | 64 => pure .I64 | 128 => pure .I128
      | _ => throw (IO.userError "bad raw integer representation")
    pure (.Fixed integer signed)
def main (args : List String) : IO Unit := do
  let [oraclePath] := args | throw (IO.userError "expected actual oracle input")
  let raw ← must (Json.parse (← IO.FS.readFile oraclePath))
  let rawTypes ← must ((← must (raw.getObjVal? "types")).getArr?)
  let rawDiscriminants ← must ((← must (raw.getObjVal? "discriminants")).getArr?)
  let oracle ← readOracle oraclePath
  let mut selected := 0
  let mut declined := 0
  for node in oracle.types do
    let .adt adt := node.shape | continue
    unless adt.kind == .enumKind do continue
    let some definition := oracle.definitions[adt.definition]? | throw (IO.userError "definition absent")
    unless definition.crateIndex == 0 do continue
    let fields ← adt.variants.mapM fun variant => variant.fields.mapM fun field => do
      let some node := oracle.types[field.typeId]? | throw (IO.userError "field absent")
      oracle.layout node
    let repr : UnivariantLayout.Representation := {
      flags := UInt8.ofNat adt.representation.flagsBits
      integerRepresentation := adt.representation.integer.isSome
      align := ← adt.representation.alignBytes.mapM (fun n => must ((Align.fromBytes (UInt64.ofNat n)).mapError reprStr))
      pack := none
      fieldShuffleSeed := UInt64.ofNat adt.representation.fieldShuffleSeed }
    let some rawType := rawTypes[node.id]? | throw (IO.userError "raw oracle type absent")
    let index ← must ((← must ((← must (rawType.getObjVal? "compiler_facts")).getObjVal? "discriminants")).getNat?)
    let some rawDiscr := rawDiscriminants[index]? | throw (IO.userError "raw oracle discriminants absent")
    let discriminants ← (← must ((← must (rawDiscr.getObjVal? "values")).getArr?)).mapM fun row => do
      let some value := (← must ((← must (row.getObjVal? "bits")).getStr?)).toNat?
        | throw (IO.userError "invalid actual discriminant bits")
      pure (BitVec.ofNat 128 value)
    let integerRepr ← adt.representation.integer.mapM integerFromRaw
    let candidate ← must (EnumLayout.compute oracle.target fields repr integerRepr discriminants)
    let actual ← oracle.layout node
    check (candidate == actual) s!"complete tagged/niche layout differs from compiler: {node.display}"
    match actual.variants with
    | .Multiple _ (.Niche ..) _ _ => selected := selected+1
    | _ => declined := declined+1
  check (selected + declined >= 10) "missing complete enum coverage"
  IO.println s!"PASS {selected} complete niche + {declined} complete tagged layouts against actual rustc"
