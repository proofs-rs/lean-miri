import Miri.Input.Reader.RuntimeQueries

namespace Miri.Input.Reader.GlobalByteReader
open Lean

private def hexBytes (value : String) : Except String (Array UInt8) := do
  let chars := value.toList.toArray
  unless chars.size % 2 == 0 do throw "global byte query has odd hex length"
  let digit := fun c =>
    if c ≥ '0' && c ≤ '9' then Except.ok (c.toNat - '0'.toNat)
    else if c ≥ 'a' && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else .error "global byte query has invalid hex"
  let mut bytes := #[]
  for i in [:chars.size / 2] do
    let some hi := chars[2*i]? | throw "global byte hex high digit absent"
    let some lo := chars[2*i+1]? | throw "global byte hex low digit absent"
    bytes := bytes.push (UInt8.ofNat (16*(← digit hi)+(← digit lo)))
  return bytes

private def legacy (catalog : Catalog) (source : Json) (path : String) : Except String GlobalByteLegacyData := do
  let ids ← (← catalog.array (← catalog.field source "covered_allocation_ids" path) path).mapM fun value => catalog.natural value path
  let rows ← catalog.array (← catalog.field source "candidates" path) path
  let candidates ← rows.mapM fun row => do
    let bytes ← hexBytes (← catalog.string (← catalog.field row "bytes_hex" path) path)
    let results ← catalog.array (← catalog.field row "salts" path) path
    unless results.size == 32 do throw "global byte candidate omits salt outcomes"
    let salts ← results.mapIdxM fun index result => do
      unless (← catalog.natural (← catalog.field result "salt" path) path) == index do throw "global byte salt index mismatch"
      let allocation ← catalog.field result "existing_allocation" path
      if (← catalog.inspect allocation path) == .null then return none
      return some (← catalog.natural (← catalog.field allocation "allocation_id" path) path)
    return (⟨bytes,salts⟩ : GlobalByteCandidateData)
  return ⟨ids,candidates⟩

/-- Source-world mode does not demand legacy coverage/candidate metadata.
The two branches retain independent typed outcomes. -/
def read (catalog : Catalog) : Except String GlobalByteQueryData := do
  let path := "$.compiler_global_byte_queries"
  let source ← catalog.field catalog.root "compiler_global_byte_queries" "$"
  unless (← catalog.string (← catalog.field source "status" path) path) == "supported" do throw "global byte compiler queries unavailable"
  unless (← catalog.natural (← catalog.field source "salt_count" path) path) == 32 do throw "global byte salt support differs from pinned source"
  let strType := do catalog.natural (← catalog.field (← catalog.field source "str_type" path) "type_id" path) path
  return ⟨legacy catalog source path,strType⟩

end Miri.Input.Reader.GlobalByteReader
