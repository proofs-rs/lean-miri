import MiriTests.Input.LegacyFixture
import Miri.Input.Decoder
import Miri.Input.RuntimeMetadata
import Miri.Input.CompilerPrimitiveFacts

open Lean Miri.Input

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

#eval do
  let text ← IO.FS.readFile "scratch/regression-inputs/u32.checked.json"
  let .ok decoded := decodeFixture text | throw (IO.userError "root_u32 decode failed")
  let .ok runtime := RuntimeMetadata.ofDocument decoded.document | throw (IO.userError "root_u32 metadata failed")
  for node in decoded.document.types do
    let .ok selected := runtime.node node.id | throw (IO.userError "type ID lookup failed")
    check (selected.id == node.id && selected.layoutId == node.layoutId) "type lookup changed its definition"
  for key in #["bool", "i8", "i16", "i32", "i64", "i128", "u8", "u16", "u32", "u64", "u128", "usize", "isize", "unit", "unit_pointer_const", "unit_pointer_mut"] do
    if let .ok physical := CompilerPrimitiveFacts.primitiveLayout runtime key then
      check (decide (runtime.lookup physical.ty = Except.ok (ε := RuntimeMetadataError) physical))
        s!"primitive {key} changed its typed layout"
  let .ok unit := CompilerPrimitiveFacts.unitLayout runtime | throw (IO.userError "unit compiler query missing")
  let .ok unitNode := runtime.node unit.ty | throw (IO.userError "unit type missing")
  check (match unitNode.shape with | .tuple elements => elements.isEmpty | _ => false)
    "compiler unit reference does not identify the empty tuple"
  check (!(CompilerPrimitiveFacts.primitiveLayout runtime "qa_missing_primitive").isOk) "missing compiler primitive accepted"
  let some first := decoded.document.types[0]? | throw (IO.userError "empty type pool")
  match RuntimeMetadata.ofDocument { decoded.document with types := decoded.document.types.push first } with
  | .error (.duplicateType id) => check (id == first.id) "duplicate type ID diagnostic changed"
  | _ => throw (IO.userError "duplicate type identity accepted")
  IO.println "compiler primitive references retain canonical typed layouts and reject missing/duplicate identities"
