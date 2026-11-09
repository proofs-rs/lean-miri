import Miri.Input.CompilerVTableFacts

/-! Exact get_vtable_ptr compiler stage from interpret/traits.rs: erase and
anonymize the complete (type,predicate-list) pair, then source has_param checks.
Symbolic allocation salt/reservation/root-pointer effects remain runtime actions.
-/
namespace Miri.Input.CompilerVTableQueries
open Lean Miri.Interpreter
structure Entry where
  inputType : TypeId
  inputPredicates : PredicateList
  outputType : TypeId
  outputPredicates : PredicateList
  typeMonomorphic : Bool
  predicatesMonomorphic : Bool
  diagnosticQueryId : Option Nat := none
structure Prepared where
  facts : CompilerFactAdapters.Prepared
  entries : Array Entry
  traceQueries : Bool := false
def prepare (facts : CompilerFactAdapters.Prepared) : Except String Prepared := do
  let mut entries := #[]
  for record in facts.context.program.input.queries.vtables do
    let input := record.inputType
    let output := record.outputType
    let _ ← facts.context.runtime.node input |>.mapError toString
    let _ ← facts.context.runtime.node output |>.mapError toString
    let before := record.inputPredicates
    let after := record.outputPredicates
    let typeMono := record.outputTypeMonomorphic
    let dynMono := record.outputPredicatesMonomorphic
    unless (← CompilerFacts.boolean facts.context output "is_monomorphic_enough") == typeMono do
      throw "vtable output monomorphization query conflict"
    if let some prior := entries.find? (fun entry => entry.inputType == input && entry.inputPredicates == before) then
      unless prior.outputType == output && prior.outputPredicates == after &&
          prior.typeMonomorphic == typeMono && prior.predicatesMonomorphic == dynMono do
        throw "conflicting complete-pair vtable erasure queries"
    else entries := entries.push ⟨input, before, output, after, typeMono, dynMono, some record.queryId⟩
  pure ⟨facts, entries, false⟩

def eraseAndAnonymize (prepared : Prepared) (ty : TypeId) (predicates : PredicateList) : Except String (TypeId × PredicateList) := do
  let found := prepared.entries.find? (fun entry => entry.inputType == ty && entry.inputPredicates == predicates)
  if prepared.traceQueries then
    let id := (found.bind (·.diagnosticQueryId)).map toString |>.getD "missing"
    dbg_trace s!"vtable_query input_type={ty} input_predicates={reprStr predicates} query_id={id}"
  let some entry := found
    | throw s!"missing exact type/predicate-pair region erasure query (type_id={ty}, predicate_ids={reprStr predicates})"
  pure (entry.outputType,entry.outputPredicates)

/-- Diagnostic output preserves the exact lookup, including missing-key errors. -/
theorem eraseAndAnonymize_trace_identity (prepared : Prepared) (ty : TypeId) (predicates : PredicateList) :
    eraseAndAnonymize {prepared with traceQueries := true} ty predicates =
      eraseAndAnonymize {prepared with traceQueries := false} ty predicates := by
  rfl

def ensureMonomorphicType (prepared : Prepared) (ty : TypeId) : Except String Unit := do
  unless (← CompilerFacts.boolean prepared.facts.context ty "is_monomorphic_enough") do
    throw "source TooGeneric: vtable concrete type has parameters"

def ensureMonomorphicDyn (prepared : Prepared) (predicates : PredicateList) : Except String Unit := do
  let matching := prepared.entries.filter (·.outputPredicates == predicates)
  let some entry := matching[0]? | throw "missing exact erased-predicate monomorphization query"
  unless matching.all (·.predicatesMonomorphic == entry.predicatesMonomorphic) do
    throw "conflicting predicate-list monomorphization queries"
  unless entry.predicatesMonomorphic do throw "source TooGeneric: vtable predicates have parameters"
private def lift (result : Except String A) : EStateM StepError S A :=
  match result with
  | .ok value => pure value
  | .error reason => throw (.unsupported s!"compiler vtable query: {reason}")

def hooks (prepared : Prepared) (base : VTableHooks P S C Fn Abi) : VTableHooks P S C Fn Abi :=
  { base with
    eraseAndAnonymize := fun _ ty dyn => lift (eraseAndAnonymize prepared ty dyn)
    ensureMonomorphicType := fun _ ty => lift (ensureMonomorphicType prepared ty)
    ensureMonomorphicDyn := fun _ dyn => lift (ensureMonomorphicDyn prepared dyn) }
end Miri.Input.CompilerVTableQueries
