import Miri.Input.Reader.Instances
import Miri.Input.Reader.Constants

namespace Miri.Input.Reader.NamedConstantReader
open Lean
abbrev Decode := MIRReader.Decode

private def supported (catalog : Catalog) (query : Json) (path : String) : Except String Unit := do
  unless (← catalog.string (← catalog.field query "status" path) path) == "supported" do
    let reason := (do catalog.string (← catalog.field query "reason" path) path).toOption
    throw s!"named compiler constant unavailable: {reason}"

private def queries (catalog : Catalog) (ctx : ConstantReader.Context) : Decode (Array NamedConstantQueryData) := do
  let records ← catalog.array (← catalog.field catalog.root "compiler_named_constants" "$") "$.compiler_named_constants"
  let mut entries := #[]
  for (record,index) in records.toList.zipIdx do
    let path := s!"$.compiler_named_constants[{index}]"
    let name ← catalog.string (← catalog.field record "name" path) path
    if entries.any (·.name == name) then throw "duplicate compiler named constant query"
    unless (← catalog.string (← catalog.field record "typing_env" path) path) == "fully_monomorphized" do
      throw "named constant compiler environment mismatch"
    let query ← catalog.field record "query" path
    let original ← get
    let origin : Decode Miri.Interpreter.CallInstance := do
      supported catalog query path
      InstanceReader.read catalog ctx.typeCount query path
    let result ← match origin.run original with
      | .error reason => pure (.error reason)
      | .ok (sourceInstance,next) =>
        set next
        pure (do
          let ty ← catalog.natural (← catalog.field (← catalog.field query "type" path) "type_id" path) path
          unless ty < ctx.typeCount do throw "named constant references missing compiler type"
          let evaluation ← catalog.field query "evaluation" path
          supported catalog evaluation path
          let value ← ConstantReader.evaluated catalog ctx ty (← catalog.field evaluation "value" path) path
          return (⟨sourceInstance,ty,value⟩ : NamedConstantValueData))
    let sourcePath := do
      (← catalog.array (← catalog.field record "path" path) path).mapM fun part => catalog.string part path
    entries := entries.push (⟨name,sourcePath,result⟩ : NamedConstantQueryData)
  return entries

def read (catalog : Catalog) (ctx : ConstantReader.Context) : Decode (Except String (Array NamedConstantQueryData)) := do
  let original ← get
  match (queries catalog ctx).run original with
  | .error reason => pure (.error reason)
  | .ok (values,next) => set next; pure (.ok values)

end Miri.Input.Reader.NamedConstantReader
