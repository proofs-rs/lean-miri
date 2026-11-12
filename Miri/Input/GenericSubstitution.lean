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

structure DefinitionIdentity where
  crateIndex : Nat
  index : Nat
  deriving Repr, DecidableEq, BEq

inductive BoundIdentity where
  | anonymous
  | named (definition : DefinitionIdentity)
  | namedForPrinting (name : String)
  | closureEnvironment
  deriving Repr, DecidableEq, BEq

inductive BoundVariable where
  | type (identity : BoundIdentity)
  | region (identity : BoundIdentity)
  | constant
  deriving Repr, DecidableEq, BEq

mutual
inductive Term where
  | parameter (sort : ArgSort) (index : Nat)
  | bound (sort : ArgSort) (index : Miri.MIR.BoundVarIndexKind) (variableIndex : Nat) (identity : BoundIdentity)
  | placeholder (sort : ArgSort) (universeIndex variableIndex : Nat) (identity : BoundIdentity)
  | inference (sort : ArgSort) (variableIndex : Nat)
  | atom (sort : ArgSort) (tag payload : String)
  | node (sort : ArgSort) (tag payload : String) (children : Terms)
  | definition (sort : ArgSort) (tag : String) (identity : DefinitionIdentity) (children : Terms)
  | binder (variables : Array BoundVariable) (value : Term)
  deriving Repr, DecidableEq, BEq

inductive Terms where
  | nil
  | cons (head : Term) (tail : Terms)
  deriving Repr, DecidableEq, BEq
end

structure FieldTemplate where
  variantIndex : Nat
  fieldIndex : Nat
  expression : Term
  deriving Repr, DecidableEq

structure DefinitionTemplate where
  parameters : Array ArgSort
  typeExpression : Term
  signatureExpression : Option Term
  fields : Array FieldTemplate
  deriving Repr, DecidableEq

def Terms.ofArray (values : Array Term) : Terms :=
  values.toList.foldr Terms.cons .nil

instance : Coe (Array Term) Terms := ⟨Terms.ofArray⟩

def Terms.mapM (f : Term → Except String Term) : Terms → Except String Terms
  | .nil => pure .nil
  | .cons head tail => return .cons (← f head) (← tail.mapM f)

def Terms.anyM (f : Term → Except String Bool) : Terms → Except String Bool
  | .nil => pure false
  | .cons head tail => do
    let found ← f head
    let rest ← tail.anyM f
    pure (found || rest)

def Term.sort : Term → ArgSort
  | .parameter sort _ | .bound sort .. | .placeholder sort ..
  | .inference sort _ | .atom sort .. | .node sort .. | .definition sort .. => sort
  | .binder _ value => value.sort

def hasParameter : Nat → Term → Except String Bool
  | 0, _ => .error "generic material parameter traversal exhausted"
  | fuel + 1, value => do
    match value with
    | .parameter .. => pure true
    | .binder _ body => hasParameter fuel body
    | .node _ _ _ children | .definition _ _ _ children =>
      children.anyM (hasParameter fuel)
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
    | .definition sort tag identity children =>
      return .definition sort tag identity (← children.mapM (shift fuel amount cutoff))
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
    | .definition sort tag identity children =>
      return .definition sort tag identity (← children.mapM (fold args fuel depth))
    | _ => pure value

/-- EarlyBinder::instantiate does no traversal when the argument list is empty,
but requires absence of early parameters. Bound-variable substitution is a
different rustc operation and is deliberately not performed here. -/
def instantiate (fuel : Nat) (args : Array Term) (value : Term) : Except String Term := do
  if args.isEmpty then
    if ← hasParameter fuel value then throw "generic material has parameters but no arguments"
    return value
  fold args fuel 0 value

def DefinitionTemplate.checkArguments (material : DefinitionTemplate) (args : Array Term) :
    Except String Unit := do
  unless args.size == material.parameters.size do
    throw "generic template argument count mismatch"
  for (argument, expected) in args.zip material.parameters do
    unless argument.sort == expected do
      throw "generic template argument sort mismatch"

def DefinitionTemplate.instantiateType (material : DefinitionTemplate) (fuel : Nat)
    (args : Array Term) : Except String Term := do
  material.checkArguments args
  instantiate fuel args material.typeExpression

def DefinitionTemplate.instantiateSignature (material : DefinitionTemplate) (fuel : Nat)
    (args : Array Term) : Except String Term := do
  material.checkArguments args
  let some source := material.signatureExpression
    | throw "generic definition has no function signature material"
  instantiate fuel args source

def DefinitionTemplate.instantiateField (material : DefinitionTemplate) (fuel : Nat)
    (args : Array Term) (variantIndex fieldIndex : Nat) : Except String Term := do
  material.checkArguments args
  let matching := material.fields.filter fun field =>
    field.variantIndex == variantIndex && field.fieldIndex == fieldIndex
  unless matching.size == 1 do throw "generic field material absent or duplicated"
  let some field := matching[0]? | throw "generic field material absent"
  instantiate fuel args field.expression

end Miri.Input.GenericSubstitution
