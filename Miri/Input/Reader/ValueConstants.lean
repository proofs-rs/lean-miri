import Miri.Input.Reader.Constants

namespace Miri.Input.Reader.ValueConstantReader
open Lean

private def typeId (catalog : Catalog) (value : Json) (path : String) : Except String MIR.TyId :=
  do catalog.natural (← catalog.field value "type_id" path) path

private def value (catalog : Catalog) (ctx : ConstantReader.Context) (record : Json) (path : String) : Except String (MIR.TyId × MIR.ConstValue) := do
  let status ← catalog.string (← catalog.field record "status" path) path
  unless status == "supported" do
    let reason : Except String (Option String) := do
      match ← catalog.optionalField record "reason" path with
      | none => pure none
      | some reason => some <$> catalog.string reason path
    throw s!"compiler intrinsic constant query failed: status={status}, reason={reprStr reason}"
  let ty ← typeId catalog (← catalog.field record "result_type" path) path
  unless ty < ctx.typeCount do throw "compiler intrinsic constant references missing result type"
  return (ty,← ConstantReader.evaluated catalog ctx ty (← catalog.field record "value" path) path)

/-- Duplicate classes compare typed outcomes only within the same input type.
Additional transport/debug fields do not change compiler query semantics. -/
def typeNames (catalog : Catalog) (ctx : ConstantReader.Context) : Except String (Array TypeNameConstantData) := do
  let path := "$.compiler_type_name_constants"
  let records ← catalog.array (← catalog.field catalog.root "compiler_type_name_constants" "$") path
  let mut rows : Array TypeNameConstantData := #[]
  let mut buckets : Std.HashMap (Option MIR.TyId) (Array TypeNameConstantData) := {}
  for record in records do
    let inputType := (do typeId catalog (← catalog.field record "input_type" path) path).toOption
    let result := do
      unless (← catalog.string (← catalog.field record "typing_env" path) path) == "fully_monomorphized" do
        throw "type_name compiler query typing environment mismatch"
      value catalog ctx record path
    let earlier := buckets[inputType]?.getD #[]
    let duplicate := earlier.find? (·.result == result)
    let key := (duplicate.map (·.sourceKey)).getD rows.size
    let row : TypeNameConstantData := ⟨inputType,key,result⟩
    if duplicate.isNone then buckets := buckets.insert inputType (earlier.push row)
    rows := rows.push row
  return rows

/-- Byte-position buckets narrow duplicate comparisons. Full typed spans are
checked before outcomes, so hygiene/file/position collisions cannot alias. -/
def callerLocations (catalog : Catalog) (ctx : ConstantReader.Context) : Except String (Array CallerLocationConstantData) := do
  let path := "$.compiler_caller_location_constants"
  let records ← catalog.array (← catalog.field catalog.root "compiler_caller_location_constants" "$") path
  let mut rows : Array CallerLocationConstantData := #[]
  let mut buckets : Std.HashMap (Nat × Nat) (Array CallerLocationConstantData) := {}
  for record in records do
    let span := do catalog.decodeSourceSpan (← catalog.field record "span" path) path
    let result := value catalog ctx record path
    let key ← match span with
      | .error _ => pure rows.size
      | .ok source =>
        let bucket := (source.lo,source.hi)
        let earlier := buckets[bucket]?.getD #[]
        let duplicate := earlier.find? fun entry => entry.span == span && entry.result == result
        let key := (duplicate.map (·.sourceKey)).getD rows.size
        if duplicate.isNone then buckets := buckets.insert bucket (earlier.push ⟨span,key,result⟩)
        pure key
    rows := rows.push ⟨span,key,result⟩
  return rows

end Miri.Input.Reader.ValueConstantReader
