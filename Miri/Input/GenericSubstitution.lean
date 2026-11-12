import Miri.MIR.Syntax

/-! Generic material trees, distinct from closed runtime TypeNode identities.
Port source: rustc 8144389c895da997dbdecaa635e41d6a50be6ffd,
rustc_type_ir/src/binder.rs::ArgFolder and fold.rs::Shifter.
Constructor payloads preserve source identities; they are never interpreted as
type names. Explicit binders distinguish locally bound and escaping variables.
This module implements early substitution, not normalization or trait solving.
The exporter/TypeArena integration is separate from this tree operation. -/
namespace Miri.Input.GenericSubstitution

inductive ArgSort where
  | type | region | constant | aggregate
  deriving Repr, DecidableEq

inductive Term where
  | parameter (sort : ArgSort) (index : Nat)
  | bound (sort : ArgSort) (index : Miri.MIR.BoundVarIndexKind) (variableIndex : Nat) (identity : String)
  | placeholder (sort : ArgSort) (universeIndex variableIndex : Nat) (identity : String)
  | inference (sort : ArgSort) (variableIndex : Nat)
  | atom (sort : ArgSort) (tag payload : String)
  | node (sort : ArgSort) (tag payload : String) (children : Array Term)
  | binder (variables : Array String) (value : Term)
  deriving Repr, BEq

def Term.sort : Term → ArgSort
  | .parameter sort _ | .bound sort .. | .placeholder sort ..
  | .inference sort _ | .atom sort .. | .node sort .. => sort
  | .binder _ value => value.sort

def hasParameter : Nat → Term → Except String Bool
  | 0, _ => .error "generic material parameter traversal exhausted"
  | fuel + 1, value => do
    match value with
    | .parameter .. => pure true
    | .binder _ body => hasParameter fuel body
    | .node _ _ _ children => do
      let mut found := false
      for child in children do found := (← hasParameter fuel child) || found
      pure found
    | _ => pure false

/-- Shifter starts at INNERMOST (zero), increments the cutoff on Binder,
and shifts only Bound indices at or above that cutoff. Canonical variables,
placeholders and variables owned by nested binders retain their identities. -/
def shift : Nat → Nat → Nat → Term → Except String Term
  | 0, _, _, _ => .error "generic material bound-variable traversal exhausted"
  | fuel + 1, amount, cutoff, value => do
    match value with
    | .bound sort (.Bound index) variableIndex identity =>
      pure (.bound sort (.Bound (if index ≥ cutoff then index + amount else index)) variableIndex identity)
    | .binder variables body => return .binder variables (← shift fuel amount (cutoff + 1) body)
    | .node sort tag payload children =>
      return .node sort tag payload (← children.mapM (shift fuel amount cutoff))
    | _ => pure value

def fold (args : Array Term) : Nat → Nat → Term → Except String Term
  | 0, _, _ => .error "generic material substitution traversal exhausted"
  | fuel + 1, depth, value => do
    -- ArgFolder::fold_ty skips the entire original type when has_param=false.
    if value.sort == .type && !(← hasParameter (fuel + 1) value) then return value
    match value with
    | .parameter sort index =>
      unless sort != .aggregate do throw "aggregate cannot be a generic parameter"
      let some replacement := args[index]? | throw "generic parameter argument is absent"
      unless replacement.sort == sort do throw "generic parameter argument sort mismatch"
      if depth == 0 then return replacement
      shift (fuel + 1) depth 0 replacement
    | .inference .region _ => throw "unexpected inference region in generic substitution"
    | .binder variables body => return .binder variables (← fold args fuel (depth + 1) body)
    | .node sort tag payload children =>
      return .node sort tag payload (← children.mapM (fold args fuel depth))
    | _ => pure value

/-- EarlyBinder::instantiate does no traversal when the argument list is empty,
but requires absence of early parameters. Bound-variable substitution is a
different rustc operation and is deliberately not performed here. -/
def instantiate (fuel : Nat) (args : Array Term) (value : Term) : Except String Term := do
  if args.isEmpty then
    if ← hasParameter fuel value then throw "generic material has parameters but no arguments"
    return value
  fold args fuel 0 value

end Miri.Input.GenericSubstitution
