import Miri.Input.CompilerForeignSymbolTables
import Miri.Input.EvalForeignConstruction

/-! Public source-facing compiler symbol hooks. The metadata parser and lookup
policy live in the lower-level CompilerForeignSymbolTables module, allowing
CompilerProviders to retain one immutable preparation result without a module
cycle. -/
namespace Miri.Input.CompilerForeignSymbols
open Miri.Interpreter

abbrev Candidate := CompilerForeignSymbolTables.Candidate
abbrev AllocatorTarget := CompilerForeignSymbolTables.AllocatorTarget
abbrev AllocatorEntry := CompilerForeignSymbolTables.AllocatorEntry
abbrev Prepared := CompilerForeignSymbolTables.Prepared

def prepare (instances : CompilerVTableRuntime.Prepared) : Except String Prepared :=
  CompilerForeignSymbolTables.prepare instances

def lookup (prepared : Prepared) (symbol : String) : Except StepError (Option Candidate) :=
  CompilerForeignSymbolTables.lookup prepared symbol

def lookupFunction (prepared : Prepared)
    (loadMir : CallInstance → EStateM StepError S LoadedBody)
    (symbol : String)
    (resolveSource : SourceSymbols.Declaration → EStateM StepError S CallInstance :=
      fun _ => throw (.unsupported "source callable requires the shared compiler World resolver")) :
    EStateM StepError S (Option (LoadedBody × CallInstance)) :=
  CompilerForeignSymbolTables.lookupFunction prepared loadMir symbol resolveSource

/-- Resolve only the selected declaration in the evaluation's shared persistent
World. A missing World is an error; this callback never creates a private cache. -/
def resolveSource (access : SourceCompilerWorld.Access S) (declaration : SourceSymbols.Declaration) :
    EStateM StepError S CallInstance := do
  let state ← get
  let some world := access.get state | throw (.unsupported "shared compiler World is not installed")
  let key ← match CompilerSourceSymbols.monoKey declaration with
    | .ok key => pure key
    | .error error => throw (.unsupported error)
  let item ← match CompilerSourceSymbols.itemDeclaration declaration with
    | .ok item => pure item
    | .error error => throw (.unsupported error)
  let item ← if let some material := world.canonical.sourceMaterial then do
    let matching := material.declarations.filter (·.definition == item.definition)
    let [retained] := matching.toList
      | throw (.unsupported "exported Item declaration absent or ambiguous in typed source universe")
    unless retained.path == item.path && retained.kind == item.kind && retained.parameters == item.parameters do
      throw (.unsupported "exported Item declaration contradicts typed source universe")
    pure retained
  else pure item
  let (world,callee) ← match SourceCompilerWorld.internItem #[item] world key with
    | .ok result => pure result
    | .error error => throw (.unsupported error)
  set (access.put state world)
  return callee

def allocatorSymbol (prepared : Prepared) (symbol : String) :
    Option (ForeignItems.AllocatorSymbol CallInstance) :=
  CompilerForeignSymbolTables.allocatorSymbol prepared symbol

def checkSymbolClash (prepared : Prepared) (symbol : String) : Except StepError Unit :=
  CompilerForeignSymbolTables.checkSymbolClash prepared symbol

def options (prepared : Prepared) (base : EvalForeignConstruction.Options) :
    EvalForeignConstruction.Options :=
  {base with noAllocShimSymbol := prepared.noAllocShimSymbol}

def hooks (prepared : Prepared) (access : SourceCompilerWorld.Access S) :
    EvalForeignConstruction.Symbols S := {
  allocatorSymbol := fun symbol => pure (allocatorSymbol prepared symbol)
  lookupFunction := fun symbol => lookupFunction prepared (CompilerCallPipeline.loadMir access) symbol (resolveSource access)
  checkSymbolClash := fun symbol => do
    match checkSymbolClash prepared symbol with
    | .ok () => pure ()
    | .error error => throw error }

end Miri.Input.CompilerForeignSymbols
