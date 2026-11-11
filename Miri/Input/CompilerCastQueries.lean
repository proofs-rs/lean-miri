import Miri.Input.CompilerCastLeaves
import Miri.Input.CompilerVTableFacts
import Miri.Input.CompilerVTableRuntime

/-! Exact compiler query closure for interpret/cast.rs. Query results are
compiler evidence keyed by complete source types/arguments; this module is not
an instance solver and does not guess trait relationships from layouts. -/
namespace Miri.Input.CompilerCastQueries
open Lean Miri.ABI Miri.MIR Miri.Memory Miri.Interpreter
abbrev Result := Except String
private def facts (p : CompilerProviders.Prepared) := p.lifecycle.calls.symbols.facts
private def layout (p : CompilerProviders.Prepared) (id : TyId) : Result LocalLayout :=
  ((facts p).context.runtime.lookup id).mapError toString

private def unique (entries : Array Catalog.CastQuery) : Result Catalog.CastQuery := do
  let some first := entries[0]? | throw "missing exact cast compiler query"
  unless entries.all (· == first) do throw "conflicting exact cast compiler queries"
  pure first

private def resolutionRecord (p : CompilerProviders.Prepared) (closure : Bool)
    (definition : DefId) (args : Array GenericArg) : Result Catalog.CastQuery := do
  let mut matching := #[]
  for record in p.program.input.queries.casts do
    let input ← match record with
      | .resolveFnPtr input _ _ => if closure then continue else pure input
      | .resolveClosureFnOnce input _ _ => if closure then pure input else continue
      | _ => continue
    let inputKind ← CompilerFactAdapters.castTypeInfo (facts p) input
    let matchesInput := match inputKind with
      | .fnDefinition source actual => !closure && source == definition && actual == args
      | .closure source actual _ => closure && source == definition && actual == args
      | _ => false
    if matchesInput then matching := matching.push record
  unique matching

def resolveFunction (p : CompilerProviders.Prepared) (definition : DefId)
    (args : Array GenericArg) : Result (Option CallInstance) := do
  let .resolveFnPtr _ _ result ← resolutionRecord p false definition args
    | throw "function resolution query kind mismatch"
  if let some id := result then
    let _ ← CompilerInstance.source p.loweringContext.instances id
  pure result

def resolveClosureFnOnce (p : CompilerProviders.Prepared) (definition : DefId)
    (args : Array GenericArg) : Result CallInstance := do
  let .resolveClosureFnOnce _ _ result ← resolutionRecord p true definition args
    | throw "closure resolution query kind mismatch"
  let _ ← CompilerInstance.source p.loweringContext.instances result
  pure result

def noBoundVars (p : CompilerProviders.Prepared) (args : Array GenericArg) : Result Bool := do
  let mut evidence := #[]
  for record in p.program.input.queries.casts do
    if let .resolveFnPtr input value _ := record then
      if let .fnDefinition _ actual ← CompilerFactAdapters.castTypeInfo (facts p) input then
        if actual == args then evidence := evidence.push value
  let some first := evidence[0]? | throw "missing exact generic arguments no_bound_vars query"
  unless evidence.all (· == first) do throw "conflicting no_bound_vars evidence"
  pure first

def lockstepTails (p : CompilerProviders.Prepared) (source target : TyId) : Result (TyId × TyId) := do
  let result ← unique (p.program.input.queries.casts.filter fun row => match row with
    | .lockstepTails a b _ _ => a == source && b == target
    | _ => false)
  let .lockstepTails _ _ source target := result | throw "lockstep query kind mismatch"
  let _ ← layout p source
  let _ ← layout p target
  pure (source,target)

def boxLayout (p : CompilerProviders.Prepared) (pointee : TyId) : Result LocalLayout := do
  let result ← unique (p.program.input.queries.casts.filter fun row => match row with
    | .boxType input _ => input == pointee | _ => false)
  let .boxType _ id := result | throw "box query kind mismatch"
  layout p id

def supertraitSlot (p : CompilerProviders.Prepared) (source target : TyId) : Result (Option Nat) := do
  let result ← unique (p.program.input.queries.casts.filter fun row => match row with
    | .supertraitSlot a b _ => a == source && b == target | _ => false)
  let .supertraitSlot _ _ slot := result | throw "supertrait query kind mismatch"
  pure slot

/-- Full predicate-list identity is the key. The principal is exported by the
compiler, not reconstructed by picking the first non-auto predicate. -/
def principal (p : CompilerProviders.Prepared) (predicates : PredicateList) : Result (Option Nat) := do
  let mut results := #[]
  for node in p.runtime.source.types do
    if node.shapeKind == .dynamicTraitObject then
      let .dynamicTraitObject ids principal _ := node.shape | throw "dynamic type shape mismatch"
      if ids == predicates then results := results.push principal
  for allocation in p.program.input.allocations do
    if let some (.vtable source) := allocation.data then
      if source.predicates == predicates then
        results := results.push source.principalPredicate
  let some first := results[0]? | throw "missing compiler principal query for exact predicate list"
  unless results.all (· == first) do throw "conflicting compiler principal queries"
  pure first

def normalizePrincipal (p : CompilerProviders.Prepared) (predicates : PredicateList) : Result (Option Nat) := do
  let some id ← principal p predicates | return none
  let entries := p.program.input.compilerPredicates.filter (·.id == id)
  let some entry := entries[0]? | throw "missing principal predicate normalization evidence"
  unless entries.all (fun row => row.normalizedId == entry.normalizedId && row.stableKey == entry.stableKey && row.autoTrait == entry.autoTrait) do throw "conflicting principal normalization evidence"
  pure (some (← CompilerVTableFacts.normalizePredicate (facts p) ⟨id,entry.stableKey,entry.autoTrait⟩))

/-- The runtime VTableEntry representation stores the target principal. The
source relation is validated by the same exact allocation-to-query resolver
used to build that entry, including query-backed source vtables that do not
appear as `.vtable` nodes in the allocation graph. -/
def eraseSelfTraitRef (p : CompilerProviders.Prepared) (token : Nat) : Result Nat := do
  let runtime := p.lifecycle.calls.symbols
  for allocation in p.program.input.allocations do
    if let some (.vtable source) := allocation.data then
      for entry in source.entries do
        if entry.kind == .supertraitVtablePointer then
          if (CompilerVTableRuntime.supertraitPrincipal runtime source.typeId entry).toOption == some token then
            return token
  for row in p.program.input.queries.vtables do
    for entry in row.metadata.entries do
      if entry.kind == .supertraitVtablePointer &&
          (CompilerVTableRuntime.supertraitPrincipal runtime row.inputType entry).toOption == some token then
        return token
  throw "missing exact exported TraitVPtr erase_self_ty relation"
private def lift (query : Result A) : RvalueM S A :=
  match query with | .ok value => pure value | .error error => throw (.unsupported s!"cast compiler query: {error}")

def required (p : CompilerProviders.Prepared) : CompilerCastLeaves.Required S C where
  requireNoBoundVars := fun _ args => do
    unless ← lift (noBoundVars p args) do
      throw (.invalidProgram "source no_bound_vars assertion failed")
  resolveFunction := fun _ definition args => lift (resolveFunction p definition args)
  resolveClosureFnOnce := fun _ definition args => lift (resolveClosureFnOnce p definition args)
  lockstepTails := fun _ source target => lift (lockstepTails p source target)
  boxLayout := fun _ ty => lift (boxLayout p ty)
  principal := fun _ token => lift (principal p token)
  supertraitSlot := fun _ source target => lift (supertraitSlot p source target)
  eraseSelfTraitRef := fun _ token => lift (eraseSelfTraitRef p token)
  normalizePrincipal := fun _ token => lift (normalizePrincipal p token)

end Miri.Input.CompilerCastQueries
