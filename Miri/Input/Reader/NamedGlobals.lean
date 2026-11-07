import Miri.Input.Reader.Regions

namespace Miri.Input.Reader.NamedGlobalReader
open Lean
abbrev Decode := MIRReader.Decode

private def value (catalog : Catalog) (typeCount allocationCount : Nat)
    (record : Json) (name path : String) : Decode NamedGlobalValueData := do
  let query ← catalog.field record "query" path
  unless (← catalog.string (← catalog.field query "status" path) path) == "supported" do
    let reason := do catalog.string (← catalog.field query "reason" path) path
    throw s!"named compiler global unavailable: {reason.toOption}"
  let payload ← catalog.field query "value" path
  let definition ← RegionReader.definition catalog (← catalog.field payload "definition" path) path
  let kind ← catalog.string (← catalog.field payload "kind" path) path
  let isStatic ← match kind with
    | "static" => pure true
    | "const_allocation" => pure false
    | _ => throw s!"named compiler global {name} has unknown allocation kind `{kind}`"
  let ty ← catalog.natural (← catalog.field (← catalog.field payload "type" path) "type_id" path) path
  unless ty < typeCount do throw "named compiler global references absent compiler type"
  let allocation ← catalog.natural (← catalog.field (← catalog.field payload "allocation" path) "allocation_id" path) path
  unless allocation < allocationCount do throw "named compiler global references absent allocation image"
  return ⟨definition,ty,allocation,isStatic⟩

private def queries (catalog : Catalog) (typeCount allocationCount : Nat) : Decode (Array NamedGlobalQueryData) := do
  let records ← catalog.array (← catalog.field catalog.root "compiler_named_statics" "$") "$.compiler_named_statics"
  let mut entries := #[]
  for (record,index) in records.toList.zipIdx do
    let path := s!"$.compiler_named_statics[{index}]"
    let name ← catalog.string (← catalog.field record "name" path) path
    let parts ← (← catalog.array (← catalog.field record "path" path) path).mapM fun part => catalog.string part path
    unless parts == #["libc",name] do throw "named compiler global path must be exactly libc::<name>"
    unless (← catalog.string (← catalog.field record "typing_env" path) path) == "fully_monomorphized" do
      throw "named global compiler environment mismatch"
    if entries.any (·.name == name) then throw "duplicate compiler named global query"
    let original ← get
    let result ← match (value catalog typeCount allocationCount record name path).run original with
      | .error reason => pure (.error reason)
      | .ok (result,next) => set next; pure (.ok result)
    entries := entries.push (⟨name,result⟩ : NamedGlobalQueryData)
  return entries

def read (catalog : Catalog) (typeCount allocationCount : Nat) : Decode (Except String (Array NamedGlobalQueryData)) := do
  let original ← get
  match (queries catalog typeCount allocationCount).run original with
  | .error reason => pure (.error reason)
  | .ok (values,next) => set next; pure (.ok values)

end Miri.Input.Reader.NamedGlobalReader
