import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceCompilerBodies
import Miri.Input.SourceCallFacts
open Lean Miri Miri.Input Miri.Interpreter Miri.Frontend.Foundation
private def checked (r : Except String α) : IO α := match r with
| .ok a => pure a | .error e => throw (IO.userError e)
private def rejects (r : Except String α) : IO Unit := match r with
| .error _ => pure () | .ok _ => throw (IO.userError "missing execution declaration facts accepted")
def main (paths : List String) : IO Unit := do
  let [path] := paths | throw (IO.userError "expected actual std snapshot")
  let document ← checked (decode (← checked (Json.parse (← IO.FS.readFile path))))
  let initial ← checked (compilerEntrySeed document)
  let mut world := initial
  for node in initial.canonical.instances do
    unless !(← checked (SourceCallFacts.isClosureLike world node.id)) do
      throw (IO.userError "ordinary source Item classified as closure")
    rejects (SourceCallFacts.codegenSymbolName world node.id)
    -- This control changes only dispatch kind to exercise the declaration
    -- attribute reader. It does not claim LLVM selection/executable MIR.
    let llvm := {node with instanceKind := .LlvmIntrinsic node.instanceKind.defId}
    let instances := world.canonical.instances.map fun row => if row.id == node.id then llvm else row
    let llvmWorld := {world with canonical := {world.canonical with instances}}
    let some source := world.canonical.sourceMaterial | throw (IO.userError "source absent")
    let some abi := source.abi | throw (IO.userError "ABI source absent")
    let some names := abi.symbolNames | throw (IO.userError "raw symbol source absent")
    let some raw := world.canonical.definitions[node.instanceKind.defId]? | throw (IO.userError "raw def absent")
    let [declaration] := (names.declarations.filter (·.definition == raw)).toList
      | throw (IO.userError "raw codegen attribute declaration absent")
    unless (← checked (SourceCallFacts.codegenSymbolName llvmWorld node.id)) == declaration.attributes.symbolName do
      throw (IO.userError "LLVM raw nullable symbol changed through mangling")
    let changedSource := {source with abi := some {abi with symbolNames := none}}
    let changed := {llvmWorld with canonical := {llvmWorld.canonical with sourceMaterial := some changedSource}}
    rejects (SourceCallFacts.codegenSymbolName changed node.id)
    let missingPhysical := {source with physical := none}
    rejects (SourceCallFacts.isClosureLike {world with canonical := {world.canonical with sourceMaterial := some missingPhysical}} node.id)
    let (updated,_) ← checked (SourceCompilerBodies.demandLoadedBody world node.id)
    world := updated
  let some closure := world.canonical.types.find? (fun row => match row.shape with | .closure .. => true | _ => false)
    | throw (IO.userError "genuine instantiated closure type absent")
  let .closure definition arguments _ := closure.shape | throw (IO.userError "closure shape absent")
  -- Evaluation-local identity only, using the genuine instantiated closure's
  -- exact definition/full arguments. No body, ABI, allocation or answer supplied.
  let node : InstanceNode := {
    id := world.canonical.instances.size
    instanceKind := .Item definition
    genericArgs := arguments
    kind := .identityOnly
    definitionId := some definition
    defPath := none
    bodyId := none
    promotedBodies := #[]}
  let closureWorld ← checked (SourceCompilerWorld.create {world.canonical with instances := world.canonical.instances.push node})
  unless (← checked (SourceCallFacts.isClosureLike closureWorld node.id)) do
    throw (IO.userError "genuine closure definition not recognized")
  rejects (SourceCallFacts.isClosureLike world world.canonical.instances.size)
  IO.println "current World ordinary/real closure kinds and raw nullable LLVM attributes pass; missing/non-LLVM cases reject"
