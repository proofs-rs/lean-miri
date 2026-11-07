import Miri.Input.Reader.Regions

namespace Miri.Input.Reader.PanicQueryReader
open Lean
abbrev Decode := MIRReader.Decode

private def parameters (catalog : Catalog) (row : Json) (path : String) : Except String (Array CompilerGenericParameter) := do
  (← catalog.array (← catalog.field row "generic_parameters" path) path).mapM fun value => do
    match ← catalog.string value path with
    | "lifetime" => pure .lifetime
    | "type_parameter" => pure .typeParameter
    | "const_parameter" => pure .constParameter
    | _ => throw "unknown compiler panic generic parameter kind"

def read (catalog : Catalog) : Decode (Option (Except String (Array PanicQueryData))) := do
  let some source ← catalog.optionalField catalog.root "compiler_panic_queries" "$" | return none
  let original ← get
  let result : Decode (Array PanicQueryData) := do
    let rows ← catalog.array source "$.compiler_panic_queries"
    let mut tags := #[]
    let mut result := #[]
    for (row,index) in rows.toList.zipIdx do
      let path := s!"$.compiler_panic_queries[{index}]"
      let tag ← catalog.string (← catalog.field row "lang_item" path) path
      if tags.contains tag then throw "duplicate panic language-item query"
      tags := tags.push tag
      let status ← catalog.string (← catalog.field row "status" path) path
      let definition ← if status != "supported" then
          pure (.error "panic language-item query unresolved")
        else do
          let value ← catalog.field row "definition" path
          if (← catalog.inspect value path) == .null then pure (.ok none)
          else pure (.ok (some (← RegionReader.definition catalog value path)))
      result := result.push (⟨tag,definition,parameters catalog row path⟩ : PanicQueryData)
    pure result
  match result.run original with
  | .ok (values,next) => set next; return some (.ok values)
  | .error reason => return some (.error reason)

end Miri.Input.Reader.PanicQueryReader
