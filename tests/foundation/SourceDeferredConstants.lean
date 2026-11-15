import Miri.Frontend.FoundationEntrySeed
import Miri.Input.SourceMirLowering
import Miri.Input.SourceCompilerConstantRequests
open Lean Miri Miri.Input Miri.Interpreter Miri.Frontend.Foundation
private def checked (value : Except String α) : IO α := match value with
  | .ok value => pure value | .error error => throw (IO.userError error)
private def rejects (value : Except String α) : IO Unit := match value with
  | .error _ => pure () | .ok _ => throw (IO.userError "uncovered constant was resolved")
private def load (world : SourceCompilerWorld.World) (name : String) (arguments : Array MIR.GenericArg := #[]) :
    Except String (SourceCompilerWorld.World × MIR.ConstOperand) := do
  let some source := world.canonical.sourceMaterial | throw "source absent"
  let [declaration] := (source.declarations.filter (·.path == name)).toList | throw "caller absent"
  let (world,callee) ← SourceCompilerWorld.internItem source.declarations world ⟨declaration.definition,arguments⟩
  let world ← SourceMirLowering.derive world callee
  let bodyId ← SourceCompilerWorld.bodyId world callee
  let some body := world.canonical.bodies[bodyId]? | throw "body absent"
  let some constant := body.requiredConsts[0]? | throw "required source constant absent"
  let .SourceRequest token ty := constant.value | throw "generic constant evaluated during body loading"
  let request ← SourceCompilerWorld.constantRequest world token
  unless request.caller == callee && request.callerArguments == arguments && request.expectedType == ty do
    throw "deferred caller/full argument/type identity changed"
  return (world,constant)
private abbrev State := MachineHooks.State Unit (Option SourceCompilerWorld.World)
private def access : SourceCompilerWorld.Access State :=
  ⟨fun s => s.machine.user,fun s w => {s with machine := {s.machine with user := some w}}⟩
private def state (world : Option SourceCompilerWorld.World) : State := {
  stack := ⟨#[]⟩
  machine := {
    memory := .empty
    borrowTracker := none
    dataRace := none
    threads := Miri.Concurrency.ThreadManager.initial false
    raceAllocations := #[]
    allocationSpans := #[]
    user := world } }

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected genuine constant entry with compiler witness")
  let document ← checked (Json.parse (← IO.FS.readFile path) >>= decode)
  let initial ← checked (compilerEntrySeed document)
  let some source := initial.canonical.sourceMaterial | throw (IO.userError "source absent")
  let some witnesses := source.constantValues | throw (IO.userError "compiler results absent")
  unless witnesses.rows.size == 1 do throw (IO.userError "fixture must provide only actual SIZE<u64> witness")
  let withoutValues := {source with constantValues := none}
  let withoutValues := {initial with canonical := {initial.canonical with sourceMaterial := some withoutValues}}
  -- Loading a selected body does not evaluate any of its constant operands.
  let (loaded,constant) ← checked (load withoutValues "main")
  rejects (SourceCompilerConstantRequests.resolve loaded constant)
  let covered := {loaded with canonical := {loaded.canonical with sourceMaterial := some source}}
  let (resolvedWorld,resolved) ← checked (SourceCompilerConstantRequests.resolve covered constant)
  let .Val (.Scalar (.Int bits bytes)) ty := resolved.value | throw (IO.userError "actual compiler scalar was lost")
  unless bits == 8 && bytes == 8 && ty == constant.value.typeId do
    throw (IO.userError "actual compiler SIZE<u64> result differs")
  -- The same generic body is reusable. Only a substituted caller whose exact
  -- key is present in the finite compiler results can resolve its operand.
  let mut covered := resolvedWorld
  for (name,available) in #[("u64",true),("u8",false)] do
    let (world,word) ← checked (SourcePhysical.intern covered (.primitive "uint" name))
    let (world,constant) ← checked (load world "unused" #[.Type word])
    covered := world
    if available then
      let (_,resolved) ← checked (SourceCompilerConstantRequests.resolve world constant)
      unless resolved.value == .Val (.Scalar (.Int 8 8)) constant.value.typeId do
        throw (IO.userError "generic caller did not use its exact concrete compiler result")
    else rejects (SourceCompilerConstantRequests.resolve world constant)
  let missing := {source with constantValues := some {rows := #[]}}
  rejects (SourceCompilerConstantRequests.resolve
    {covered with canonical := {covered.canonical with sourceMaterial := some missing}} constant)
  match SourceCompilerConstantRequests.consume access constant (state (some covered)) with
  | .ok actual after =>
    unless actual == resolved && after.machine.memory.nextAllocId == 1 && after.machine.memory.live.isEmpty do
      throw (IO.userError "scalar consumption changed value or allocated guest memory")
  | .error error _ => throw (IO.userError (reprStr error))
  match SourceCompilerConstantRequests.consume access constant (state none) with
  | .error (.unsupported _) _ => pure ()
  | _ => throw (IO.userError "source request silently created or replaced a missing World")
  -- Already concrete Val operands do not require or write a source World.
  match SourceCompilerConstantRequests.consume access resolved (state none) with
  | .ok actual after =>
    unless actual == resolved && after.machine.user.isNone do throw (IO.userError "Val path touched World")
  | .error error _ => throw (IO.userError (reprStr error))
  IO.println "compiler scalar witness consumed on demand; generic substitutions use exact keys; missing key/World reject; Val unchanged"
