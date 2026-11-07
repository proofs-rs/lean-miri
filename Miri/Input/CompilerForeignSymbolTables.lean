import Miri.Interpreter.ForeignItems
import Miri.Input.CompilerVTableRuntime
import Miri.Input.CompilerCallPipeline

/-! Immutable compiler symbol and allocator-shim tables. This module contains
only source metadata decoding and exact lookup policy, so preparation can be
cached by the compiler provider without depending on runtime foreign hooks. -/
namespace Miri.Input.CompilerForeignSymbolTables
open Miri.Interpreter

abbrev Candidate := ForeignSymbolCandidate
abbrev AllocatorTarget := ForeignAllocatorTarget
abbrev AllocatorEntry := ForeignAllocatorEntry
abbrev Prepared := ForeignSymbolsData

/-- The reader preserves source symbol iteration order and compiler identity. -/
def prepare (instances : CompilerVTableRuntime.Prepared) : Except String Prepared :=
  instances.facts.context.program.input.mirTables.foreignSymbols

private def earlierSpan (left right : Candidate) : Bool :=
  left.spanLo < right.spanLo ||
    (left.spanLo == right.spanLo && left.spanHi < right.spanHi)

/-- Miri's lookup_exported_symbol weak/strong precedence and duplicate error.
The array order is the pinned iterator order, including local-crate-first and
linked dependency order. Equal-strength duplicate definitions terminate. -/
def lookup (prepared : Prepared) (symbol : String) : Except StepError (Option Candidate) := do
  let mut selected : Option Candidate := none
  for candidate in prepared.candidates do
    if candidate.explicitSymbol && candidate.symbol == symbol then
      if let some previous := selected then
        match candidate.weak, previous.weak with
        | false, true => selected := some candidate
        | true, false => pure ()
        | _, _ =>
          let (first,second) := if earlierSpan previous candidate then
              (previous,candidate) else (candidate,previous)
          throw (StepError.machineStop s!"multiple symbol definitions `{symbol}` in crates {first.crateName} and {second.crateName}")
      else selected := some candidate
  return selected

/-- Exact lookup_exported_fn type guard. Loading MIR is a separate canonical
CompilerCallPipeline operation, and its missing-body error is preserved. -/
def lookupFunction (prepared : Prepared)
    (loadMir : CallInstance → EStateM StepError S LoadedBody)
    (symbol : String) : EStateM StepError S (Option (LoadedBody × CallInstance)) := do
  let candidate? ← match lookup prepared symbol with
    | .ok result => pure result
    | .error error => throw error
  let some candidate := candidate? | return none
  if candidate.kind != .function && candidate.kind != .associatedFunction then
    throw (.undefinedBehavior "attempt to call an exported symbol that is not defined as a function")
  let some fnInstance := candidate.fnInstance | throw (.unsupported "callable exported symbol has no compiler instance identity")
  return some (← loadMir fnInstance,fnInstance)

def allocatorSymbol (prepared : Prepared) (symbol : String) :
    Option (ForeignItems.AllocatorSymbol CallInstance) :=
  (prepared.allocatorEntries.find? (·.symbol == symbol)).map fun entry =>
    match entry.target with
    | .redirect target => .redirect target
    | .special method => .special method

/-- Source sig.rs exemption: compiler-builtins definitions do not clash with
Miri's built-in implementation. Every other exact exported candidate does. -/
def checkSymbolClash (prepared : Prepared) (symbol : String) :
    Except StepError Unit := do
  match ← lookup prepared symbol with
  | none => pure ()
  | some candidate =>
    if candidate.compilerBuiltins then pure ()
    else throw (StepError.machineStop s!"symbol shim clashing `{symbol}` at {candidate.crateName}:{candidate.spanLo}..{candidate.spanHi}")

end Miri.Input.CompilerForeignSymbolTables
