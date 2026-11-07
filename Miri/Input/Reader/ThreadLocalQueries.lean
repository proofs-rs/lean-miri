import Miri.Input.Reader.MIRState
import Miri.Input.Reader.AllocationMemory

namespace Miri.Input.Reader.ThreadLocalQueryReader
open Lean Miri.MIR

private def info (catalog : Catalog) (input : Json) (path : String) : Except String ThreadLocalStaticInfo := do
  let field := fun key => catalog.field input key path
  let natural := fun key => do catalog.natural (← field key) path
  let boolean := fun key => do catalog.boolean (← field key) path
  return {
    status := DecoderValues.parseStatus (← catalog.string (← field "status") path)
    sizeBytes := ← natural "size_bytes"
    alignBytes := ← natural "align_bytes"
    mutability := match ← catalog.string (← field "mutability") path with
      | "mutable" => .mutable | "immutable" => .immutable | tag => .unknown tag
    isStatic := ← boolean "is_static"
    foreignItem := ← boolean "is_foreign_item"
    threadLocal := ← boolean "thread_local"
    nested := boolean "nested" }

private def query (catalog : Catalog) (definition : DefId) (source : DefinitionId)
    (input : Json) (path : String) : Except String ThreadLocalQueryData := do
  let data ← info catalog (← catalog.field input "global_info" path) path
  unless data.status == .supported && data.isStatic && data.threadLocal do
    throw "TLS declaration compiler query evidence is unresolved or inconsistent"
  let initializer ← catalog.field input "initializer" path
  let memory ← if data.foreignItem then pure none else do
    unless (← catalog.string (← catalog.field initializer "status" path) path) == "supported" do
      throw "TLS initializer query failed"
    pure (some (← catalog.readAllocationMemory (← catalog.field initializer "allocation" path) path))
  return ⟨definition,source,data,memory⟩

def register (catalog : Catalog) (definition : DefId) (input : Json) (path : String) : MIRReader.Decode Unit := do
  let state ← get
  let result := do
    let some source := state.compiler.definitions[definition]? | throw "TLS canonical definition absent"
    query catalog definition source input path
  set {state with threadLocals := state.threadLocals.push (definition,result)}

private def sameNested (left right : Except String Bool) : Bool :=
  match left,right with
  | .ok left,.ok right => left == right
  | .error _,.error _ => true
  | _,_ => false

private def sameInfo (left right : ThreadLocalStaticInfo) : Bool :=
  left.status == right.status && left.sizeBytes == right.sizeBytes && left.alignBytes == right.alignBytes &&
  left.mutability == right.mutability && left.isStatic == right.isStatic &&
  left.foreignItem == right.foreignItem && left.threadLocal == right.threadLocal && sameNested left.nested right.nested

private def compileRows (rows : Array (DefId × Except String ThreadLocalQueryData))
    (selected : Option DefId) : Except String (Array ThreadLocalQueryData) := do
  let mut found := #[]
  for (definition,result) in rows do
    if let some wanted := selected then
      unless definition == wanted do continue
    let data ← result
    if let some previous := found.find? (fun row : ThreadLocalQueryData => row.definition == definition) then
      unless sameInfo previous.info data.info && previous.initializer == data.initializer do
        throw "conflicting compiler TLS query evidence"
    else found := found.push data
  return found

/-- Source compiler queries have already been decoded while reading their MIR
nodes. Finalization builds a definition-indexed array, preserving per-definition
failures without demanding unrelated TLS initializer queries. -/
def finish (state : MIRReader.State) : ThreadLocalTable := Id.run do
  let entries := state.compiler.definitions.mapIdx fun definition _ =>
    if !state.threadLocals.any (·.1 == definition) then none else some do
      let rows ← compileRows state.threadLocals (some definition)
      let some row := rows[0]? | throw "missing exact compiler TLS declaration/initializer evidence"
      pure row
  return ⟨entries,compileRows state.threadLocals none⟩

end Miri.Input.Reader.ThreadLocalQueryReader
