import Miri.Input.EvalRuntimeConstruction

/-! Exact compiler startup facts and the small source-owned arguments adapter.
These are separate from host environment contents: the latter remain the
explicit `EvalBootstrap.Configuration` supplied by the embedding. -/
namespace Miri.Input.EvalStartupRuntimeConstruction
open Lean Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

structure StartupFacts where
  noCore : Except String Bool
  coreEscapeDefault : Except String (DefinitionId × Bool)

private def field (value : Json) (name : String) : Except String Json :=
  value.getObjVal? name

private def fieldString (value : Json) (name : String) : Except String String := do
  (← field value name).getStr?

private def fieldNat (value : Json) (name : String) : Except String Nat := do
  (← field value name).getNat?

/-- Prepare source facts from the pinned exporter query table. The escape-default identity must already be in the canonical
definition table; no path or display-name identity is synthesized here. -/
def prepare (compiler : CompilerProviders.Prepared) : Except String StartupFacts := do
  let queries ← field compiler.program.input.raw "compiler_runtime_queries"
  let startup ← field queries "startup"
  let noCore := do
    let value ← field startup "no_core"
    value.getBool?
  let coreEscapeDefault := do
    let value ← field startup "core_escape_default"
    let rawDefinition ← field value "definition"
    let source : DefinitionId := ⟨← fieldNat rawDefinition "crate", ← fieldNat rawDefinition "index"⟩
    let available ← (← field value "mir_available").getBool?
    pure (source,available)
  return ⟨noCore, coreEscapeDefault⟩

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
