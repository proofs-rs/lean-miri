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
private def records (p : CompilerProviders.Prepared) : Result (Array CastQueryData) :=
  p.program.input.mirTables.castQueries
private def unique (entries : Array CastQueryData) : Result CastQueryData := do
  let some first := entries[0]? | throw "missing exact cast compiler query"
  unless entries.all (·.identity == first.identity) do throw "conflicting exact cast compiler queries"
  pure first
private def query (p : CompilerProviders.Prepared) (kind : String) (source : TyId) : Result CastQueryValue := do
  let row ← unique ((← records p).filter fun record =>
    record.kind.toOption == some kind && record.inputType.toOption == some source)
  row.value
private def pairQuery (p : CompilerProviders.Prepared) (kind : String) (source target : TyId) : Result CastQueryValue := do
  let row ← unique ((← records p).filter fun record =>
    record.kind.toOption == some kind &&
    record.inputSource.toOption == some source && record.inputTarget.toOption == some target)
  row.value
private def layout (p : CompilerProviders.Prepared) (id : TyId) : Result LocalLayout :=
  ((facts p).context.runtime.lookup id).mapError toString

private def resolutionRecord (p : CompilerProviders.Prepared) (kind : String)
    (definition : DefId) (args : Array GenericArg) : Result CastQueryData := do
  let mut matching := #[]
  for record in ← records p do
    if record.kind.toOption == some kind then
      let input ← record.inputType
      let inputKind ← CompilerFactAdapters.castTypeInfo (facts p) input
      let matchesInput := match inputKind with
        | .fnDefinition source actual => kind == "resolve_fn_ptr" && source == definition && actual == args
        | .closure source actual _ => kind == "resolve_closure_fn_once" && source == definition && actual == args
        | _ => false
      if matchesInput then matching := matching.push record
  unique matching
def resolveFunction (p : CompilerProviders.Prepared) (definition : DefId)
    (args : Array GenericArg) : Result (Option CallInstance) := do
  let .resolved result ← (← resolutionRecord p "resolve_fn_ptr" definition args).value
    | throw "function resolution cast query has wrong result kind"
  result.mapM p.program.input.mirTables.instance

def resolveClosureFnOnce (p : CompilerProviders.Prepared) (definition : DefId)
    (args : Array GenericArg) : Result CallInstance := do
  let .resolved (some id) ← (← resolutionRecord p "resolve_closure_fn_once" definition args).value
    | throw "closure resolution cast query has no instance"
  p.program.input.mirTables.instance id

def noBoundVars (p : CompilerProviders.Prepared) (args : Array GenericArg) : Result Bool := do
  let mut evidence := #[]
  for record in ← records p do
    if record.kind.toOption == some "resolve_fn_ptr" then
      let input ← record.inputType
      if let .fnDefinition _ actual ← CompilerFactAdapters.castTypeInfo (facts p) input then
        if actual == args then
          record.environment
          evidence := evidence.push (← record.noBoundVars)
  let some first := evidence[0]? | throw "missing exact generic arguments no_bound_vars query"
  unless evidence.all (· == first) do throw "conflicting no_bound_vars evidence"
  pure first

def lockstepTails (p : CompilerProviders.Prepared) (source target : TyId) : Result (TyId × TyId) := do
  let .tails source target ← pairQuery p "lockstep_tails" source target
    | throw "lockstep tails cast query has wrong result kind"
  let _ ← layout p source
  let _ ← layout p target
  pure (source,target)

def boxLayout (p : CompilerProviders.Prepared) (pointee : TyId) : Result LocalLayout := do
  let .boxType id ← query p "box_type" pointee
    | throw "box cast query has wrong result kind"
  layout p id

def supertraitSlot (p : CompilerProviders.Prepared) (source target : TyId) : Result (Option Nat) := do
  let .supertraitSlot slot ← pairQuery p "supertrait_slot" source target
    | throw "supertrait cast query has wrong result kind"
  return slot

def principal (p : CompilerProviders.Prepared) (token : Nat) : Result (Option Nat) := do
  let value ← (facts p).dynamicPredicates.lookup token |>.mapError (fun id => s!"invalid predicate list {id}")
  let some principal := value.principal | throw "explicit compiler principal evidence absent"
  return principal

def normalizePrincipal (p : CompilerProviders.Prepared) (token : Nat) : Result (Option Nat) := do
  let some id ← principal p token | return none
  let entry ← CompilerVTableFacts.evidence (facts p) id
  pure (some (← CompilerVTableFacts.normalizePredicate (facts p) ⟨id,entry.stableKey,entry.autoTrait⟩))

/-- The runtime VTableEntry representation stores the target principal. The
source relation is validated by the same exact allocation-to-query resolver
used to build that entry, including query-backed source vtables that do not
appear as `.vtable` nodes in the allocation graph. -/
def eraseSelfTraitRef (p : CompilerProviders.Prepared) (token : Nat) : Result Nat := do
  let runtime := p.lifecycle.calls.symbols
  let tables := p.program.input.vtableTables
  for allocation in p.program.input.allocations do
    if let some (.vtable source) := allocation.data then
      let some (some id) := tables.allocationMetadata[allocation.id]? | throw "vtable metadata absent"
      let metadata ← tables.metadata.lookup id |>.mapError (fun id => s!"invalid vtable metadata {id}")
      let entries ← tables.entryLists.lookup metadata.entries |>.mapError (fun id => s!"invalid vtable entries {id}")
      for entry in entries do
        if entry.status == .supported && entry.kind == .supertraitVtablePointer then
          if (CompilerVTableRuntime.supertraitPrincipal runtime source.typeId entry).toOption == some token then
            return token
  for source in tables.queries do
    let row ← source
    let some id := row.metadata | continue
    let metadata ← tables.metadata.lookup id |>.mapError (fun id => s!"invalid vtable metadata {id}")
    unless metadata.status == .supported do continue
    let entries ← tables.entryLists.lookup metadata.entries |>.mapError (fun id => s!"invalid vtable entries {id}")
    for entry in entries do
      if entry.status == .supported && entry.kind == .supertraitVtablePointer &&
          (CompilerVTableRuntime.supertraitPrincipal runtime row.inputTypeId entry).toOption == some token then
        return token
  throw "compiler Self-erasure relation for principal absent"
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
