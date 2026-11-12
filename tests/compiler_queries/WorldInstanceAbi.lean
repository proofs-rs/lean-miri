import Miri.Input.Decoder
import Miri.Input.CompilerInstanceAbi

/-! Fresh pinned rustc ABI correspondence, then the same complete keys outside
an empty instance prefix and with every imported ABI result removed. -/
open Miri.Input
private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh source instance ABI fixture")
  let document := (← must (decodeJson (← IO.FS.readFile path))).document
  let runtime ← must ((RuntimeMetadata.ofDocument document).mapError toString)
  let initial ← must ((RuntimeArrayTypes.create runtime).mapError reprStr)
  let mut checked := 0
  for row in document.queries.instanceAbis do
    let some node := document.instances[row.instanceId]? | throw (IO.userError "missing instance")
    let .Item definition := node.instanceKind | continue
    let some source := document.definitions[definition]? | continue
    let some rawPath := source.rawPath | continue
    unless rawPath.components.back?.bind (·.name) == some "identity" do continue
    let (actual,_) ← must ((WorldInstanceAbi.construct row.instanceId row.extraArgumentTypes).run initial)
    let expected ← must (CallResolution.functionAbiId runtime row.abiId)
    unless actual == expected do
      throw (IO.userError s!"raw ABI differs from pinned rustc for instance {row.instanceId}:\n{reprStr actual}\n{reprStr expected}")
    let store ← must (InstanceArena.Store.ofSource initial.arena #[])
    let key ← must (InstanceArena.Key.ofSource initial.arena node.instanceKind node.genericArgs)
    let (callee,store) ← must (store.intern initial.arena key)
    unless callee == 0 do throw (IO.userError "constructed ABI instance did not append densely")
    let source := {runtime.source with functionAbis := #[], queries := {runtime.source.queries with instanceAbis := #[]}}
    let world := {initial with instances := store, metadata := {runtime with source}}
    let (novel,after) ← must ((WorldInstanceAbi.construct callee row.extraArgumentTypes).run world)
    unless novel == expected && after.instances.constructed == world.instances.constructed do
      throw (IO.userError "constructed instance ABI used numeric material capability or lost World")
    let noPolicy := {source with definitions := source.definitions.map (fun defn => {defn with functionAbiMaterial := none})}
    let invalid := {world with metadata := {world.metadata with source := noPolicy, checkedMaterial := none}}
    if ((WorldInstanceAbi.construct callee row.extraArgumentTypes).run invalid).isOk then
      throw (IO.userError "missing raw panic/codegen policy was accepted")
    checked := checked + 1
  unless checked == 10 do throw (IO.userError s!"only {checked} raw generic scalar ABI cases compared")
  IO.println s!"PASS {checked} complete pinned-rustc ABI comparisons, constructed keys without result catalogs, missing policy rejection"
