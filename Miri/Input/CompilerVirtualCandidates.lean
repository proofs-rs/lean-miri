import Lean

/-! Demand-time access to the producer's virtual-instance candidate index.
The index uses the dense compiler instance ID directly. A null slot has no
virtual candidate evidence; an empty array is an explicit empty candidate set.
The index is evidence for joining exact query rows; membership alone does not
resolve a virtual call or certify the receiver's vtable. -/
namespace Miri.Input.CompilerVirtualCandidates
open Lean

/-- The source stays opaque until a particular instance demands its candidates.
Construction performs no scan, decoding or substitution of index entries. -/
structure Catalog where
  private mk ::
  private source : Json
  deriving Inhabited

def ofJson (source : Json) : Catalog := ⟨source⟩

private def field (source : Json) (key path : String) : Except String Json :=
  source.getObjVal? key |>.mapError fun error => s!"{path}.{key}: {error}"

/-- Check only the demanded instance's row. IDs are strictly increasing,
unique, and refer to existing positions in the finalized compiler query table.
Unrelated instance entries are neither parsed nor treated as successful facts. -/
def Catalog.lookup (catalog : Catalog) (instanceId instanceCount queryCount : Nat) :
    Except String (Array Nat) := do
  let path := "$.compiler_virtual_candidates"
  let version ← (← field catalog.source "schema_version" path).getNat?
    |>.mapError fun error => s!"{path}.schema_version: {error}"
  unless version == 1 do throw s!"{path}.schema_version: expected 1"
  let byInstance ← (← field catalog.source "by_instance" path).getArr?
    |>.mapError fun error => s!"{path}.by_instance: {error}"
  unless byInstance.size == instanceCount do
    throw s!"{path}.by_instance: expected {instanceCount} dense instance slots"
  let rowPath := s!"{path}.by_instance[{instanceId}]"
  let some row := byInstance[instanceId]? | throw s!"{rowPath}: instance ID is out of range"
  if row == .null then throw s!"{rowPath}: virtual candidate row was not supplied"
  let values ← row.getArr? |>.mapError fun error => s!"{rowPath}: {error}"
  let mut result := #[]
  let mut previous : Option Nat := none
  for index in [:values.size] do
    let some value := values[index]? | throw s!"{rowPath}[{index}]: candidate index is out of range"
    let id ← value.getNat? |>.mapError fun error => s!"{rowPath}[{index}]: {error}"
    unless id < queryCount do throw s!"{rowPath}[{index}]: candidate query {id} is out of range"
    if let some prior := previous then
      unless prior < id do throw s!"{rowPath}[{index}]: candidate query IDs must be strictly increasing"
    result := result.push id
    previous := some id
  return result

/-- A caller must present its actual compiler query ID; a missing index row or
an unrelated query never becomes a permissive virtual-dispatch default. -/
def Catalog.requireMember (catalog : Catalog) (instanceId instanceCount queryId queryCount : Nat) :
    Except String Unit := do
  let candidates ← catalog.lookup instanceId instanceCount queryCount
  unless candidates.contains queryId do
    throw s!"$.compiler_virtual_candidates.by_instance[{instanceId}]: exact query {queryId} is absent"

private def referenceKey (source : Json) (path : String) :
    Except String (Nat × Array Nat) := do
  let input ← field source "input_type" path
  let typeId ← (← field input "type_id" s!"{path}.input_type").getNat?
  let predicates ← (← field source "input_predicates" path).getArr?
  let mut ids := #[]
  for index in [:predicates.size] do
    let some predicate := predicates[index]?
      | throw s!"{path}.input_predicates[{index}]: predicate index is out of range"
    let id ← (← field predicate "predicate_id" s!"{path}.input_predicates[{index}]").getNat?
    ids := ids.push id
  return (typeId, ids)

/-- Join a demanded virtual row to the finalized exact compiler-query table.
The ID, source type and ordered predicate identities must all agree; index
membership is never a replacement for these compiler-key checks. -/
def Catalog.query (catalog : Catalog) (instanceId instanceCount : Nat) (queries : Array Json)
    (reference : Json) : Except String Json := do
  let path := "virtual.vtable_query"
  let id ← (← field reference "query_id" path).getNat?
  catalog.requireMember instanceId instanceCount id queries.size
  let some row := queries[id]? | throw s!"{path}: missing finalized compiler query {id}"
  let rowPath := s!"$.compiler_vtable_queries[{id}]"
  unless (← (← field row "query_id" rowPath).getNat?) == id do
    throw s!"{rowPath}: query identity does not match its catalog position"
  unless (← referenceKey reference path) == (← referenceKey row rowPath) do
    throw s!"{path}: exact compiler type/predicate key differs from query {id}"
  return row

end Miri.Input.CompilerVirtualCandidates
