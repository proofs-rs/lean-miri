import Miri.Frontend.FoundationSignatureFnAbi
import Miri.Input.Decoder

open Lean Miri Miri.Frontend.Foundation

private def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

/-- Compare independently exported compiler FnAbi modes and full physical
layouts for a fresh monomorphic pointer identity. Pool IDs are never equated. -/
def main (paths : List String) : IO Unit := do
  let [foundationPath, compilerPath] := paths
    | throw (IO.userError "expected foundation and ordinary exports of pointer identity")
  let document ← checked (Json.parse (← IO.FS.readFile foundationPath) >>= decode)
  let some body := document.bodies[0]? | throw (IO.userError "source body absent")
  let definition ← checked (body.getObjValAs? Nat "definition")
  let (physical, computed) ← checked (rustFunctionAbiOfSourceSignature document definition #[])
  let compiler ← checked (Input.decodeJson (← IO.FS.readFile compilerPath))
  let doc := compiler.document
  let some root := doc.bodyRoots[0]? | throw (IO.userError "compiler root absent")
  let some row := doc.queries.instanceAbis.find? (fun row => row.instanceId == root.entryInstance && row.extraArgumentTypes.isEmpty)
    | throw (IO.userError "compiler instance ABI absent")
  let some actual := doc.functionAbis[row.abiId]? | throw (IO.userError "compiler ABI absent")
  unless computed.arguments.size == actual.arguments.size &&
      computed.callingConvention == actual.callingConvention && computed.canUnwind == actual.canUnwind &&
      computed.cVariadic == actual.cVariadic && computed.fixedCount == actual.fixedCount do
    throw (IO.userError "computed pointer ABI header differs from compiler")
  let target ← checked (runtimeTargetOfTarget document.target)
  for (computedArg, actualArg) in (computed.arguments.push computed.returnValue).zip
      (actual.arguments.push actual.returnValue) do
    unless computedArg.mode == actualArg.mode do
      throw (IO.userError "computed pointer pass mode/attributes differ from compiler")
    let computedLayout ← checked (physical.runtimeLayout computedArg.typeId)
    let some sourceLayout := doc.layouts[actualArg.layoutId]? | throw (IO.userError "compiler physical layout absent")
    let actualLayout ← checked ((Input.RuntimeMetadata.layout target sourceLayout).mapError toString)
    unless computedLayout.layout == actualLayout do
      throw (IO.userError "computed pointer physical layout differs from compiler")
  IO.println "foundation pointer FnAbi: exact mode/attributes and full physical layouts match fresh compiler export"
