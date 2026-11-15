import Miri.Frontend.Foundation
import Miri.Input.Model.SourceAllocationIdentity

/-! Decode the observation-only initial allocation map once. No JSON survives
this boundary, and absence does not assert an empty compiler dedup map. -/
namespace Miri.Frontend.Foundation.SourceAllocationIdentityParser
open Lean
private def kind : String → Except String Input.SourceAllocationIdentity.Kind
  | "memory" => pure .memory | "static" => pure .static | "function" => pure .function
  | "vtable" => pure .vtable | "type_id" => pure .typeId
  | _ => throw "unsupported allocation identity global kind"
private def raw (value : Json) (field : String) : Except String UInt64 := do
  let number ← value.getObjValAs? Nat field
  unless number < 2^64 do throw "allocation identity raw number exceeds u64"
  return UInt64.ofNat number

def material (source : Json) (typeCount : Nat) :
    Except String (Option Input.SourceAllocationIdentity.Material) := do
  let value ← match source.getObjVal? "allocation_identity_source" with
    | .ok value => pure value
    | .error _ => return none
  if value == Json.null then return none
  let globals ← (← value.getObjValAs? (Array Json) "globals").mapM fun row => do
    return ({rawId := ← raw row "source_alloc_id",kind := ← kind (← row.getObjValAs? String "kind")} : Input.SourceAllocationIdentity.Global)
  let dedup ← (← value.getObjValAs? (Array Json) "dedup").mapM fun row => do
    let key ← row.getObjVal? "key"
    let keyKind ← kind (← key.getObjValAs? String "kind")
    let decodedKey : Input.SourceAllocationIdentity.Key ← (do
      if keyKind == .vtable then
        let type ← key.getObjValAs? Nat "type"
        let dynamicType ← key.getObjValAs? Nat "dynamic_type"
        pure (.vtable type dynamicType)
      else pure (.unavailable keyKind))
    return ({rawId := ← raw row "source_alloc_id",salt := ← raw row "salt",key := decodedKey} : Input.SourceAllocationIdentity.Dedup)
  let result : Input.SourceAllocationIdentity.Material := {frontier := ← raw value "frontier",globals,dedup}
  result.validate typeCount
  return some result
end Miri.Frontend.Foundation.SourceAllocationIdentityParser
