import Miri.Input.GenericSubstitution
import Miri.Input.GenericSyntax
import Std.Data.HashMap

/-! Query-local variance constraints from raw declarations. Port of pinned
rustc_hir_analysis/src/variance/{terms,constraints,solve}.rs. No inferred
variance, relation answer or cross-execution cache enters the source material. -/
namespace Miri.Input.VarianceInference
open GenericSubstitution
open Miri.MIR (Variance)

def meet : Variance → Variance → Variance
  | .Invariant, _ | _, .Invariant => .Invariant
  | .Covariant, .Contravariant | .Contravariant, .Covariant => .Invariant
  | .Bivariant, value | value, .Bivariant => value
  | value, _ => value

def compose : Variance → Variance → Variance
  | .Bivariant, _ => .Bivariant
  | .Invariant, _ => .Invariant
  | .Covariant, value => value
  | .Contravariant, .Covariant => .Contravariant
  | .Contravariant, .Contravariant => .Covariant
  | .Contravariant, .Invariant => .Invariant
  | .Contravariant, .Bivariant => .Bivariant

structure Declaration where
  parameters : Array ArgSort
  fields : Array Term
  signature : Option Term
  langItem : Option String
  deriving Repr

inductive Expression where
  | constant (value : Variance)
  | variable (index : Nat)
  | transform (outer inner : Expression)
  deriving Repr

structure Entry where
  identity : DefinitionIdentity
  source : Declaration
  start : Nat
  deriving Repr

structure Constraint where
  index : Nat
  expression : Expression
  deriving Repr

private structure Collection where
  entries : Array Entry := #[]
  indices : Std.HashMap (Nat × Nat) Nat := {}
  constraints : Array Constraint := #[]
  count : Nat := 0

private abbrev CollectM := StateT Collection (Except String)

private def lift (value : Except String α) : CollectM α :=
  match value with | .ok value => pure value | .error error => throw error

private def ensure (lookup : DefinitionIdentity → Except String Declaration)
    (identity : DefinitionIdentity) : CollectM Entry := do
  let key := (identity.crateIndex,identity.index)
  if let some index := (← get).indices[key]? then
    let some entry := (← get).entries[index]? | throw "variance declaration index is absent"
    return entry
  let source ← lift (lookup identity)
  unless source.parameters.all (· != .aggregate) do
    throw "variance declaration has an aggregate generic parameter"
  unless source.signature.isNone || source.fields.isEmpty do
    throw "variance declaration combines function signature and ADT fields"
  let state ← get
  let entry := Entry.mk identity source state.count
  set {state with
    entries := state.entries.push entry
    indices := state.indices.insert key state.entries.size
    count := state.count + source.parameters.size}
  pure entry

private def constrain (entry : Entry) (sort : ArgSort) (index : Nat)
    (expression : Expression) : CollectM Unit := do
  let some expected := entry.source.parameters[index]? | throw "variance parameter index is absent"
  unless expected == sort do throw "variance parameter sort mismatch"
  modify fun state => {state with constraints := state.constraints.push ⟨entry.start + index,expression⟩}

private def invariant (expression : Expression) :=
  Expression.transform expression (.constant .Invariant)

private def children (terms : Terms) : Array Term := Id.run do
  let rec loop : Terms → List Term
    | .nil => [] | .cons value rest => value :: loop rest
  return (loop terms).toArray

private def inspect (lookup : DefinitionIdentity → Except String Declaration)
    (aliases : DefinitionIdentity → Array Term → Except String Term)
    (entry : Entry) : Nat → Array (Array BoundVariable) → Expression → Term → CollectM Unit
  | 0, _, _, _ => throw "variance source traversal exhausted"
  | fuel + 1, scopes, variance, term => do
    let descend := inspect lookup aliases entry fuel scopes
    let inspectArgs := fun (values : Array Term) (ambient : Expression) => do
      for value in values do descend ambient value
    match term with
    | .atom .type _ _ | .atom .region "static" "" | .bound .region .. => pure ()
    | .atom .aggregate "pattern_not_null" "" => pure ()
    | .definition .type "foreign" _ .nil | .definition .aggregate "auto_trait" _ .nil => pure ()
    | .parameter .type index => constrain entry .type index variance
    | .parameter .region index => constrain entry .region index variance
    | .parameter .constant index =>
      unless entry.source.parameters[index]? == some .constant do
        throw "variance constant parameter is absent or has the wrong sort"
    | .binder variables body => inspect lookup aliases entry fuel (scopes.push variables) variance body
    | .definition .type "adt" identity arguments =>
      let arguments := children arguments
      let source ← lift (lookup identity)
      unless source.signature.isNone do throw "ADT variance source has a function role"
      unless arguments.size == source.parameters.size do throw "variance nominal argument count mismatch"
      for (argument,index) in arguments.zipIdx do
        unless some argument.sort == source.parameters[index]? do throw "variance nominal argument sort mismatch"
      if ← lift ((Terms.ofArray arguments).anyM (hasParameter (fuel + 1))) then
        let target ← ensure lookup identity
        for (argument,index) in arguments.zipIdx do
          let ambient := if argument.sort == .constant then variance
            else .transform variance (.variable (target.start + index))
          descend ambient argument
      else inspectArgs arguments variance
    | .definition .type tag identity arguments =>
      let arguments := children arguments
      if tag == "alias_free_rigid" || tag == "alias_free_not_rigid" then
        let expanded ← lift (aliases identity arguments)
        lift (GenericSyntax.validateInBinders {
          parameters := entry.source.parameters
          boundTypes := false
          boundConstants := false} (fuel + 1) scopes .type expanded)
        descend variance expanded
      else if tag.startsWith "alias_" then inspectArgs arguments (invariant variance)
      else throw s!"unnameable nominal constructor in variance source: {tag}"
    | .definition .constant tag _ arguments =>
      if tag.startsWith "alias_" then inspectArgs (children arguments) (invariant variance)
      else throw "unsupported constant definition in variance source"
    | .node .constant _ _ _ => pure ()
    | .node .type tag payload terms =>
      let values := children terms
      if tag == "reference" then
        let #[region,pointee] := values | throw "variance reference source arity"
        descend variance region
        unless payload == "mutable" || payload == "immutable" do
          throw "variance reference source mutability"
        descend (if payload == "mutable" then invariant variance else variance) pointee
      else if tag == "raw_pointer" then
        let #[pointee] := values | throw "variance pointer source arity"
        unless payload == "mutable" || payload == "immutable" do
          throw "variance pointer source mutability"
        descend (if payload == "mutable" then invariant variance else variance) pointee
      else if tag == "tuple" || tag == "slice" || tag == "array" || tag == "pattern" ||
          tag == "unsafe_binder" || tag == "function_pointer" then
        inspectArgs values variance
      else if tag == "dynamic" then
        for value in values do
          if value.sort == .region then descend variance value
          else descend (invariant variance) value
      else throw s!"unsupported type constructor in variance source: {tag}"
    | .node .aggregate "signature" _ terms =>
      let values := children terms
      unless !values.isEmpty do throw "variance signature has no output"
      for (value,index) in values.zipIdx do
        descend (if index + 1 == values.size then variance
          else .transform variance (.constant .Contravariant)) value
    | .node .aggregate tag _ terms =>
      if tag == "pattern_range" || tag == "pattern_or" then inspectArgs (children terms) variance
      else throw s!"unsupported aggregate in variance source: {tag}"
    | .definition .aggregate "trait" _ terms => inspectArgs (children terms) (invariant variance)
    | .definition .aggregate "projection" _ terms =>
      let values := children terms
      let some output := values.back? | throw "variance existential projection has no term"
      descend (.constant .Invariant) output
    | _ => throw "unsupported parameter-bearing syntax in variance source"

private def overrideVariance (source : Declaration) : Option Variance :=
  if source.langItem == some "phantom_data" || source.langItem == some "covariant_unsafe_cell" then
    some .Covariant
  else if source.langItem == some "unsafe_cell" then some .Invariant
  else none

private def collect (lookup : DefinitionIdentity → Except String Declaration)
    (aliases : DefinitionIdentity → Array Term → Except String Term)
    (fuel : Nat) (root : DefinitionIdentity) : Except String Collection := do
  let action : CollectM Unit := do
    let _ ← ensure lookup root
    let mut cursor := 0
    let mut remaining := fuel
    while cursor < (← get).entries.size do
      if remaining == 0 then throw "variance declaration dependency worklist exhausted"
      remaining := remaining - 1
      let some entry := (← get).entries[cursor]? | throw "variance source worklist entry is absent"
      let policy : GenericSyntax.Policy := {
        parameters := entry.source.parameters, boundTypes := false, boundConstants := false }
      for field in entry.source.fields do
        lift (GenericSyntax.validate policy fuel .type field)
      if let some signature := entry.source.signature then
        lift (GenericSyntax.validate policy fuel .signature signature)
      unless (overrideVariance entry.source).isSome do
        for field in entry.source.fields do
          inspect lookup aliases entry fuel #[] (.constant .Covariant) field
        if let some signature := entry.source.signature then
          inspect lookup aliases entry fuel #[] (.constant .Covariant) signature
      cursor := cursor + 1
  pure (← action.run {}).2

private def evaluate (solutions : Array Variance) : Expression → Except String Variance
  | .constant value => pure value
  | .variable index => match solutions[index]? with
    | some value => pure value | none => throw "variance solution variable is absent"
  | .transform outer inner => return compose (← evaluate solutions outer) (← evaluate solutions inner)

private def checkedSet (values : Array α) (index : Nat) (value : α) : Except String (Array α) :=
  if bounded : index < values.size then pure (values.set index value bounded)
  else throw "variance update index is absent"

private def solve (collection : Collection) : Except String (Array Variance) := do
  let mut solutions := Array.replicate collection.count Variance.Bivariant
  for entry in collection.entries do
    if let some variance := overrideVariance entry.source then
      unless entry.source.parameters == #[.type] do throw "variance lang-item parameter domain mismatch"
      solutions := (← checkedSet solutions entry.start variance)
  let mut remaining := 2 * collection.count + 1
  let mut changed := true
  while changed do
    if remaining == 0 then throw "variance lattice failed to stabilize"
    remaining := remaining - 1
    changed := false
    for constraint in collection.constraints do
      let some old := solutions[constraint.index]? | throw "variance constrained variable is absent"
      let next := meet old (← evaluate solutions constraint.expression)
      if old != next then
        solutions := (← checkedSet solutions constraint.index next)
        changed := true
  pure solutions

/-- Infer only the declaration dependency closure demanded by this query.
The finite lattice permits at most two strict changes per parameter. -/
def query (lookup : DefinitionIdentity → Except String Declaration)
    (aliases : DefinitionIdentity → Array Term → Except String Term)
    (fuel : Nat) (root : DefinitionIdentity) : Except String (Array Variance) := do
  let collection ← collect lookup aliases fuel root
  let solutions ← solve collection
  let some entry := collection.entries[0]? | throw "variance root declaration is absent"
  let mut result := solutions.extract entry.start (entry.start + entry.source.parameters.size)
  for (sort,index) in entry.source.parameters.zipIdx do
    if sort == .constant || (entry.source.signature.isSome && result[index]? == some .Bivariant) then
      result := (← checkedSet result index .Invariant)
  pure result

end Miri.Input.VarianceInference
