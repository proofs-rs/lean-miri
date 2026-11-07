import Miri.Input.EvalRuntimeConstruction

/-! Exact compiler startup facts and the small source-owned arguments adapter.
These are separate from host environment contents: the latter remain the
explicit `EvalBootstrap.Configuration` supplied by the embedding. -/
namespace Miri.Input.EvalStartupRuntimeConstruction
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

abbrev StartupFacts := StartupQueryData

/-- Demand the reader-owned startup table. Individual query failures stay
stored until the corresponding source startup path asks for them. -/
def prepare (compiler : CompilerProviders.Prepared) : Except String StartupFacts :=
  compiler.program.input.mirTables.startupQueries

private def demanded (query : Except String A) : MachineHooks.M K U A :=
  match query with
  | .ok value => pure value
  | .error reason => throw (.unsupported reason)

/-- Attach exact exporter-derived no_core and sentinel-MIR facts to the argv
constructor from the same fixed execution Config. No target knob is supplied
by the caller, and failed compiler queries remain demand-time Unknown. -/
def argumentsFromExecution
    (compiler : CompilerProviders.Prepared)
    (execution : EvalExecutable.Core Os R P H D O Aff B Host C ClockHost)
    (facts : StartupFacts) :
    Except String (EntryArguments.Hooks MiriMemoryKind
      (ThreadStacks.Storage (EvalExecutable.U Os R P H D O Aff B Host))
      (ValidityMachine.Control (ThreadStacks.Storage (EvalRuntimeConstruction.W Os R P H D O Aff B Host)))
      P C) :=
  let result := EvalRuntimeConstruction.argumentsFromExecution compiler execution false
    (demanded (facts.coreEscapeDefault.map Prod.snd))
  let windows := compiler.externStatics.targetFacts.map fun target => target.os == "windows"
  do
    let hooks ← result
    let windows ← windows
    pure {hooks with windows, isNoCore := demanded facts.noCore}

end Miri.Input.EvalStartupRuntimeConstruction
