import Miri.Input.Reader.Instances

namespace Miri.Input.Reader.CastQueryReader
open Lean Miri.MIR

private def typeId (catalog : Catalog) (count : Nat) (input : Json) (path : String) : Except String TypeId := do
  let id ← catalog.natural (← catalog.field input "type_id" path) path
  unless id < count do throw s!"{path}: invalid cast type ID {id}"
  return id

private def readValue (catalog : Catalog) (typeCount instanceCount : Nat)
    (instances : Array (Except String Miri.Interpreter.CallInstance))
    (input : Json) (path kind : String) (environment : Except String Unit) : MIRReader.Decode CastQueryValue := do
  environment
  let status ← catalog.string (← catalog.field input "status" path) path
  unless status == "supported" do
    let reason := (do catalog.string (← catalog.field input "reason" path) path).toOption
    throw s!"{path}: compiler cast query unavailable (status {status}): {reason}"
  let value ← catalog.inspect (← catalog.field input "value" path) path
  match kind with
  | "resolve_fn_ptr" | "resolve_closure_fn_once" =>
    if value == .null then return .resolved none
    let id ← catalog.natural (← catalog.field value "instance_id" path) path
    unless id < instanceCount do throw s!"{path}: invalid cast instance ID {id}"
    let supplied ← InstanceReader.read catalog typeCount value path
    let some actual := instances[id]? | throw s!"{path}: cast instance absent"
    unless supplied == (← actual) do throw s!"{path}: cast instance metadata disagrees with canonical instance"
    return .resolved (some id)
  | "lockstep_tails" =>
    return .tails (← typeId catalog typeCount (← catalog.field value "source_tail" path) path)
      (← typeId catalog typeCount (← catalog.field value "target_tail" path) path)
  | "box_type" => return .boxType (← typeId catalog typeCount value path)
  | "supertrait_slot" =>
    let slot ← if value == .null then pure none else some <$> catalog.natural value path
    return .supertraitSlot slot
  | _ => throw s!"{path}: unsupported cast query {kind}"

/-- Query identity depends on consumed typed evidence. Unused malformed keys
and optional flags have one absent meaning, independent of diagnostic paths.
The typed result retains success, unsupported reasons and checked failures. -/
private def equivalent (left right : CastQueryData) : Bool :=
  left.kind.toOption == right.kind.toOption &&
  left.inputType.toOption == right.inputType.toOption &&
  left.inputSource.toOption == right.inputSource.toOption &&
  left.inputTarget.toOption == right.inputTarget.toOption &&
  left.environment.toOption == right.environment.toOption &&
  left.noBoundVars.toOption == right.noBoundVars.toOption &&
  left.value == right.value

/-- Complete instances are referenced by the canonical instance table, never
redecoded or relowered while resolving a cast. Inline metadata is checked once
against that table; failed rows retain their errors without interning identities. -/
def read (catalog : Catalog) (typeCount : Nat)
    (instances : Array (Except String Miri.Interpreter.CallInstance)) : MIRReader.Decode (Array CastQueryData) := do
  let instanceCount := instances.size
  let rows ← catalog.array (← catalog.field catalog.root "compiler_cast_queries" "$") "cast queries"
  let mut result := #[]
  let mut candidates : Std.HashMap (Option String × Option Nat × Option Nat × Option Nat) (Array Nat) := {}
  for (input,index) in rows.toList.zipIdx do
    let path := s!"cast queries[{index}]"
    let field := fun key => catalog.field input key path
    let kind : Except String String := do catalog.string (← field "query_kind") path
    let inputType : Except String TypeId := do typeId catalog typeCount (← field "input_type") path
    let inputSource : Except String TypeId := do typeId catalog typeCount (← field "input_source") path
    let inputTarget : Except String TypeId := do typeId catalog typeCount (← field "input_target") path
    let readEnvironment := fun path => (show Except String Unit from do
      unless (← catalog.string (← catalog.field input "typing_env" path) path) == "fully_monomorphized" do
        throw "cast query typing environment mismatch")
    let environment := readEnvironment path
    let noBoundVars : Except String Bool := do catalog.boolean (← field "args_no_bound_vars") path
    let action : MIRReader.Decode CastQueryValue := do
      -- Results use a stable diagnostic path so identical checked failures
      -- remain the same semantic result when exported at different row indices.
      let path := "cast query value"
      let kind ← catalog.string (← catalog.field input "query_kind" path) path
      readValue catalog typeCount instanceCount instances input path kind (readEnvironment path)
    let value : Except String CastQueryValue ← match action.run (← get) with
      | .ok (value,next) => set next; pure (.ok value)
      | .error reason => pure (.error reason)
    let row : CastQueryData := ⟨index,kind,inputType,inputSource,inputTarget,environment,noBoundVars,value⟩
    let key := (kind.toOption,inputType.toOption,inputSource.toOption,inputTarget.toOption)
    let previousRows := candidates[key]?.getD #[]
    let mut identity := index
    for previous in previousRows do
      let some previousRow := result[previous]? | throw "cast query identity candidate is outside the typed table"
      if equivalent previousRow row then
        identity := previousRow.identity
        break
    candidates := candidates.insert key (previousRows.push index)
    result := result.push {row with identity := identity}
  return result

end Miri.Input.Reader.CastQueryReader
