import Miri.Input.Reader.GlobalBytes

open Lean Miri.Input Miri.Input.Reader

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)
private def reference (id : Nat) : Json := Json.mkObj [("$lean_miri_shared_ref",toJson id)]
private def read (source : Json) (nodes : Array Json := #[]) : IO GlobalByteQueryData := do
  let root := Json.mkObj [("shared_payloads",Json.mkObj [("schema_version",toJson (2 : Nat)),("nodes",Json.arr nodes)]),
    ("compiler_global_byte_queries",source)]
  let catalog ← must (Catalog.parse root)
  must (GlobalByteReader.read catalog)

def main : IO Unit := do
  let salts := (Array.range 32).map fun index => Json.mkObj [("salt",toJson index),
    ("existing_allocation",if index == 0 then Json.mkObj [("allocation_id",toJson (0 : Nat))] else .null)]
  let candidate := Json.mkObj [("bytes_hex",reference 0),("salts",reference 1)]
  let source := Json.mkObj [("status",toJson "supported"),("salt_count",toJson (32 : Nat)),
    ("str_type",Json.mkObj [("type_id",toJson (0 : Nat))]),
    ("covered_allocation_ids",Json.arr #[toJson (0 : Nat)]),("candidates",Json.arr #[reference 2])]
  let data ← read source #[toJson "6162",Json.arr salts,candidate]
  let legacy ← must data.legacy
  let some candidate := legacy.candidates[0]? | throw (IO.userError "global byte candidate missing")
  unless (← must data.strType) == 0 && legacy.coveredAllocationIds == #[0] &&
      candidate.bytes == #[97,98] && candidate.salts.size == 32 &&
      candidate.salts[0]? == some (some 0) && candidate.salts[1]? == some none do
    throw (IO.userError "shared global byte metadata changed")
  let sourceWorld ← read (Json.mkObj [("status",toJson "supported"),("salt_count",toJson (32 : Nat)),
    ("str_type",Json.mkObj [("type_id",toJson (0 : Nat))])])
  unless (← must sourceWorld.strType) == 0 && sourceWorld.legacy.toOption.isNone do
    throw (IO.userError "source-world metadata demanded legacy candidates")
