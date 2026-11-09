import Miri.Input.Decoder
import Miri.Input.LowerMIR

open Lean Miri.Input

private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: fields.toList.filter (fun item => item.1 != key)))

private def reject (input : Json) (label : String) : IO Unit := do
  check (!(decodeJson input.compress).isOk) s!"{label}: importer accepted invalid input"

def main : IO Unit := do
  let source ← must (Json.parse (← IO.FS.readFile "tests/input/fixtures/strict-unit.json"))
  let input ← must (decodeJson source.compress)
  let some firstType := input.document.types[0]? | throw (IO.userError "missing first type")
  let some firstInstance := input.document.instances[0]? | throw (IO.userError "missing first instance")
  check (firstType.layoutId == 0 && firstInstance.id == 0)
    "different pool spaces did not preserve index zero"
  let recursive ← must (Json.parse "{\"kind\":\"expression\",\"expression_kind\":\"function_call\",\"arguments\":[{\"kind\":\"const\",\"value\":0}]}")
  let recursiveInput ← must (set source "type_constants" (.arr #[recursive]))
  let recursiveDecoded ← must (decodeJson recursiveInput.compress)
  check (decide (recursiveDecoded.document.typeConstants[0]? = some (.Expr .FunctionCall #[.Const 0])))
    "recursive constant ID was expanded or rewritten"
  reject (← must (set source "type_constants" (.arr #[recursive, recursive]))) "duplicate canonical constant definitions"
  let definitions ← must ((source.getObjVal? "definitions").bind Json.getArr?)
  reject (← must (set source "definitions" (.arr (definitions.push definitions[0]!)))) "duplicate compiler definition identities"
  let layouts ← must ((source.getObjVal? "layouts").bind Json.getArr?)
  let equalLayouts ← must (set source "layouts" (.arr (layouts.push layouts[0]!)))
  let equalLayouts ← must (decodeJson equalLayouts.compress)
  check (equalLayouts.document.layouts.size == layouts.size + 1) "equal physical payloads collapsed distinct layout IDs"
  let dangling ← must (Json.parse "{\"kind\":\"alias\",\"rigidity\":\"rigid\",\"alias_kind\":\"free\",\"def_id\":0,\"generic_args\":[{\"kind\":\"const\",\"value\":42}]}")
  reject (← must (set source "type_constants" (.arr #[dangling]))) "unused out of bounds constant definition"
  let badDefinition ← must (Json.parse "{\"kind\":\"alias\",\"rigidity\":\"rigid\",\"alias_kind\":\"free\",\"def_id\":99999,\"generic_args\":[]}")
  reject (← must (set source "type_constants" (.arr #[badDefinition]))) "out of bounds definition ID"
  let roots ← must ((source.getObjVal? "body_roots").bind Json.getArr?)
  for key in #["body", "entry_instance"] do
    let badRoot ← must (set roots[0]! key (toJson (99999 : Nat)))
    reject (← must (set source "body_roots" (.arr (roots.set! 0 badRoot)))) s!"out of bounds root {key} ID"
  let types ← must ((source.getObjVal? "types").bind Json.getArr?)
  let badDynamic ← must (Json.parse "{\"kind\":\"dynamic_trait_object\",\"predicates\":[99999],\"principal_predicate\":99999,\"region\":{\"kind\":\"erased\"}}")
  let badType ← must (set types[0]! "shape" badDynamic)
  reject (← must (set source "types" (.arr (types.set! 0 badType)))) "out of bounds predicate ID"
  let allocations ← must ((source.getObjVal? "allocations").bind Json.getArr?)
  let badReference ← must (Json.parse "{\"storage_offset_bytes\":0,\"target\":99999,\"target_offset_encoded_bytes\":\"0000000000000000\",\"immutable\":false,\"shared_ref\":false}")
  let withRelocation ← must (set allocations[0]! "size_bytes" (toJson (8 : Nat)))
  let withRelocation ← must (set withRelocation "bytes_hex" (.str "0000000000000000"))
  let initialized ← must (Json.parse "{\"start_bytes\":0,\"end_bytes_exclusive\":8,\"state\":\"initialized\"}")
  let withRelocation ← must (set withRelocation "initialization_ranges" (.arr #[initialized]))
  let withRelocation ← must (set withRelocation "relocations" (.arr #[badReference]))
  reject (← must (set source "allocations" (.arr (allocations.set! 0 withRelocation)))) "out of bounds allocation ID"
  let second ← must (set allocations[0]! "allocation_id" (toJson (1 : Nat)))
  let duplicated ← must (set source "allocations" (.arr (allocations.push second)))
  let imported ← must (decodeJson duplicated.compress)
  let some secondAllocation := imported.document.allocations[1]? | throw (IO.userError "missing second allocation")
  check (imported.document.allocations.size == 2 && secondAllocation.id == 1)
    "equal bytes collapsed distinct allocations"
  let types ← must ((source.getObjVal? "types").bind Json.getArr?)
  for invalid in #[toJson (types.size + 10), .str "bad", toJson (-1 : Int), Json.mkObj [("layout_id", toJson (0 : Nat))]] do
    let bad ← must (set types[0]! "layout" invalid)
    reject (← must (set source "types" (.arr (types.set! 0 bad)))) "invalid layout reference"
  reject (← must (set source "fn_abis" (.arr #[Json.mkObj []]))) "unused malformed ABI definition"
  reject (← must (set source "spans" (.arr #[Json.mkObj []]))) "unused malformed span definition"
  reject (← must (set source "schema_version" (toJson (3 : Nat)))) "obsolete root schema"
  IO.println "typed pools preserve ID spaces and allocation identity; all definitions and references are checked"
