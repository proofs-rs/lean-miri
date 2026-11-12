import Miri.Input.CompilerCallPipeline
import Miri.Input.CompilerShimAbi
import Miri.Interpreter.Backtrace

/-! Exact compiler type/ABI/symbolic-function leaves for backtrace.rs.
Source-map, hygiene and symbol-rendering services remain required; no name or
line number is inferred from diagnostic spellings or a nearby exported span. -/
namespace Miri.Input.CompilerBacktraceFacts
open Miri.ABI Miri.Memory Miri.Interpreter
abbrev Result := Except String

private def lift (result : Result A) : EStateM StepError S A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.unsupported s!"compiler backtrace query: {error}")

private def liftWorld (result : Result A) : TypeArena.WorldM A :=
  match result with | .ok value => pure value | .error message => throw message

def unitPointerLayout (prepared : CompilerCallPipeline.Prepared) : TypeArena.WorldM LocalLayout := do
  let unit ← liftWorld (CompilerFacts.unitLayout prepared.symbols.facts.context)
  let pointer ← CompilerRuntimeQueries.mutPointerType prepared.runtime unit.ty
  RuntimeMetadata.layoutInWorld prepared.calls.runtime pointer

/-- Only an actual ADT receives the source repr(C) check. A known non-ADT
returns None; unavailable type/repr metadata is an error, not a non-ADT default. -/
def adtReprC (_prepared : CompilerCallPipeline.Prepared) (ty : MIR.TyId) :
    TypeArena.WorldM (Option Bool) := do
  let world ← get
  match ← liftWorld (world.lookupType ty) with
  | .material node => match node.shape with
    | .adt data => pure (some data.representation.c)
    | _ => pure none
  | .constructed (.adt definition _) =>
    let reference ← liftWorld (world.definitionRef definition)
    let some source := world.definitions[reference]? | throw "backtrace ADT definition absent"
    let some declaration := source.adtDeclaration | throw "backtrace ADT source declaration absent"
    pure (some declaration.representation.c)
  | .constructed _ => pure none

def hooks (prepared : CompilerCallPipeline.Prepared) (types : RuntimeArrayQueries.Access S)
    (shim : CompilerShimAbi.Prepared)
    (image : AllocationImage.Imported) (memory : S → MemoryState P Extra K)
    (base : Backtrace.Hooks P S D MD B I E Loc) : Backtrace.Hooks P S D MD B I E Loc :=
  { base with
    foreign := CompilerShimAbi.hooks shim base.foreign
    unitPointerLayout := RuntimeArrayQueries.perform types (unitPointerLayout prepared)
    globalFunction := fun id => do
      lift (CompilerVTableRuntime.globalFunction prepared.symbols image (memory (← get)) id) }

def reprCHook (prepared : CompilerCallPipeline.Prepared) (types : RuntimeArrayQueries.Access S)
    (ty : MIR.TyId) : EStateM StepError S (Option Bool) :=
  RuntimeArrayQueries.perform types (adtReprC prepared ty)

end Miri.Input.CompilerBacktraceFacts
