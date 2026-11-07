import Miri.Input.Reader.MIRState
import Miri.Input.Reader.Catalog

namespace Miri.Input.Reader.RetagQueryReader
open Lean

private abbrev Row := Except String (DefinitionId × Except String Bool)

private def select (rows : Array Row) (wanted : Option DefinitionId) : Except String Bool := do
  let mut seen : Std.HashSet (Nat × Nat) := {}
  let mut selected := none
  for row in rows do
    let (key,value) ← row
    let pair := (key.crateIndex,key.index)
    if seen.contains pair then throw "duplicate compiler retag definition query"
    seen := seen.insert pair
    if wanted == some key then selected := some (← value)
  let some value := selected | throw "exact compiler retag frame attribute query absent"
  return value

private def row (catalog : Catalog) (input : Json) (path : String) : Row := do
  let definition ← catalog.field input "definition" path
  let key : DefinitionId := ⟨← catalog.natural (← catalog.field definition "crate" path) path,
    ← catalog.natural (← catalog.field definition "index" path) path⟩
  let value := do
    unless (← catalog.string (← catalog.field input "status" path) path) == "supported" do
      throw "compiler rustc_no_writable attribute query unavailable"
    catalog.boolean (← catalog.field input "rustc_no_writable" path) path
  return (key,value)

/-- Compile each demanded definition's exact ordered outcome once. The absent
outcome retains malformed or duplicate row failures for later appended keys.
Consumers use a checked canonical-definition array lookup. -/
def read (catalog : Catalog) : MIRReader.Decode (Except String RetagAttributeTable) := do
  try
    let path := "$.compiler_retag_queries"
    let inputs ← catalog.array (← catalog.field catalog.root "compiler_retag_queries" "$") path
    let rows := inputs.mapIdx fun index input => row catalog input s!"{path}[{index}]"
    let mut state ← get
    for result in rows do
      let .ok (definition,_) := result | continue
      let key := (definition.crateIndex,definition.index)
      unless state.definitions.contains key do
        let index := state.compiler.definitions.size
        state := {state with
          definitions := state.definitions.insert key index
          compiler := {state.compiler with definitions := state.compiler.definitions.push definition}}
    set state
    return .ok ⟨state.compiler.definitions.map (fun key => (key,select rows (some key))),select rows none⟩
  catch reason => return .error reason

end Miri.Input.Reader.RetagQueryReader
