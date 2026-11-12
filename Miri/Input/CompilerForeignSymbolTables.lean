import Miri.Interpreter.ForeignItems
import Miri.Input.CompilerVTableRuntime
import Miri.Input.CompilerCallPipeline

/-! Immutable compiler symbol and allocator-shim tables. This module contains
only source metadata decoding and exact lookup policy, so preparation can be
cached by the compiler provider without depending on runtime foreign hooks. -/
namespace Miri.Input.CompilerForeignSymbolTables
open Miri.Interpreter

structure Candidate where
  symbol : String
  explicitSymbol : Bool
  /-- Only callable exports need a MIR instance. Statics/non-callables must
  still participate in symbol clashes and in the exported-function UB guard. -/
  fnInstance : Option CallInstance
  crateIndex : Nat
  crateName : String
  weak : Bool
  spanLo : Nat
  spanHi : Nat
  kind : ForeignItems.ExportKind
  compilerBuiltins : Bool
  deriving Repr, DecidableEq

inductive AllocatorTarget where
  | redirect (symbol : String)
  | special (method : ForeignItems.SpecialAllocatorMethod)
  deriving Repr, DecidableEq

structure AllocatorEntry where
  symbol : String
  target : AllocatorTarget
  deriving Repr, DecidableEq

structure Prepared where
  noAllocShimSymbol : String
  /-- Exact `iter_exported_symbols` iteration order; do not sort this array. -/
  candidates : Array Candidate
  allocatorEntries : Array AllocatorEntry
  deriving Repr, DecidableEq

private def exportKind (value : String) : Except String ForeignItems.ExportKind :=
  match value with
  | "function" => pure .function
  | "associated_function" => pure .associatedFunction
  | "static" => pure .staticItem
  | "other" => pure .other
  | _ => throw s!"unknown exported symbol definition kind `{value}`"

private def allocatorTarget : Catalog.AllocatorTarget → Except String AllocatorTarget
  | .redirect symbol => pure (.redirect symbol)
  | .special method => match method with
    | "alloc" => pure (.special .Alloc)
    | "alloc_zeroed" => pure (.special .AllocZeroed)
    | "dealloc" => pure (.special .Dealloc)
    | "realloc" => pure (.special .Realloc)
    | _ => throw s!"unknown compiler special allocator method `{method}`"

def prepare (instances : CompilerVTableRuntime.Prepared) : Except String Prepared := do
  let program := instances.facts.context.program
  let source := program.input.queries.runtime.foreignSymbols
  let some records := source.exportedCandidates | throw "compiler exported candidates absent"
  let ctx := LowerContext.ofDocument program.input
  let mut candidates := #[]
  let mut previousIndex : Option Nat := none
  for record in records do
    if let some previous := previousIndex then
      unless previous < record.iterationIndex do
        throw "exported symbol iterator order is missing or inconsistent"
    previousIndex := some record.iterationIndex
    let kind ← exportKind record.definitionKind
    let callee ← if kind == .function || kind == .associatedFunction then do
      let some id := record.instanceId | throw "exported callable instance absent"
      let _ ← CompilerInstance.Material.source ctx.instances id
      pure (some id)
    else pure none
    let some span := program.input.spans[record.span]? | throw "exported symbol span ID out of bounds"
    candidates := candidates.push {
      symbol := record.symbol
      explicitSymbol := record.explicitSymbol
      fnInstance := callee
      crateIndex := record.crateIndex
      crateName := record.crateName
      weak := record.weak
      spanLo := span.lo
      spanHi := span.hi
      kind := kind
      compilerBuiltins := record.compilerBuiltins }
  let mut allocatorEntries := #[]
  for (symbol, target) in source.allocatorShims do
    let entry : AllocatorEntry := ⟨symbol, ← allocatorTarget target⟩
    if allocatorEntries.any (·.symbol == entry.symbol) then
      throw s!"duplicate compiler allocator shim symbol `{entry.symbol}`"
    allocatorEntries := allocatorEntries.push entry
  return ⟨source.noAllocShimSymbol, candidates, allocatorEntries⟩

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
