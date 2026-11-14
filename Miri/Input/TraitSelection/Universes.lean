import Miri.Input.TraitSelection.Material

/-! Higher-ranked binder opening and placeholder visibility. Pinned source:
`rustc_infer/src/infer/relate/higher_ranked.rs::enter_forall_and_leak_universe`
creates placeholders in a fresh universe before creating candidate inference
variables. Removing one binder also decrements escaping de Bruijn indices, while
nested binders retain their own variables. These operations do not implement
region constraints, candidate inference, leak checking or a complete trait query.
No caller may classify a higher-ranked goal from binder opening alone. -/
namespace Miri.Input.TraitSelection.Universes
open GenericSubstitution

structure Scope where
  outer : Nat
  current : Nat
  deriving Repr, DecidableEq

/-- A new query-local universeIndex; callers retain the greatest allocated index. -/
def enter (lastAllocated : Nat) : Scope := ⟨lastAllocated,lastAllocated + 1⟩

private def boundVariable (variables : Array BoundVariable) (index : Nat) : Except String (ArgSort × BoundIdentity) := do
  let some value := variables[index]? | throw "higher-ranked bound variable index is absent"
  pure (match value with
    | .type identity => (.type,identity)
    | .region identity => (.region,identity)
    | .constant => (.constant,.anonymous))

/-- Open precisely one binder. `depth` counts binders nested inside that binder;
indices above it are shifted down after its removal. Canonical variables belong
to another namespace and cannot be mistaken for de Bruijn bound variables. -/
def openTerm (variables : Array BoundVariable) (universeIndex : Nat) :
    Nat → Nat → Term → Except String Term
  | 0, _, _ => .error "higher-ranked binder opening traversal exhausted"
  | fuel + 1, depth, value => do
    match value with
    | .bound sort (.Bound index) position identity =>
      if index < depth then return value
      if index == depth then
        let (expected,identity) ← boundVariable variables position
        unless expected == sort do throw "higher-ranked binder variable sort mismatch"
        return .placeholder sort universeIndex position identity
      return .bound sort (.Bound (index - 1)) position identity
    | .bound _ .Canonical .. => throw "canonical bound variable is not a higher-ranked binder variable"
    | .binder inner body => return .binder inner (← openTerm variables universeIndex fuel (depth + 1) body)
    | .node sort tag payload children =>
      return .node sort tag payload (← children.mapM (openTerm variables universeIndex fuel depth))
    | .definition sort tag identity children =>
      return .definition sort tag identity (← children.mapM (openTerm variables universeIndex fuel depth))
    | _ => pure value

private def openPredicate (variables : Array BoundVariable) (universeIndex fuel : Nat)
    (predicate : Predicate) : Except String Predicate := do
  let term := openTerm variables universeIndex fuel 0
  let reference (value : TraitRef) : Except String TraitRef := do
    pure {value with arguments := ← value.arguments.mapM term}
  match predicate with
  | .trait goal => return .trait {goal with traitRef := ← reference goal.traitRef}
  | .equal left right => return .equal (← term left) (← term right)
  | .projection kind definition arguments expected =>
    return .projection kind definition (← arguments.mapM term) (← term expected)
  | .regionOutlives longer shorter => return .regionOutlives (← term longer) (← term shorter)
  | .typeOutlives ty region => return .typeOutlives (← term ty) (← term region)
  | .constEvaluatable value => return .constEvaluatable (← term value)
  | .constHasType value ty => return .constHasType (← term value) (← term ty)
  | .wellFormed value => return .wellFormed (← term value)
  | .hostEffect requiresConst value => return .hostEffect requiresConst (← reference value)
  | .unstableFeature feature => return .unstableFeature feature

/-- Opening a quantified obligation yields a clause with no outer binder. It
still requires inference and fulfillment in the returned universeIndex. -/
def openClause (scope : Scope) (fuel : Nat) (clause : Clause) : Except String Clause := do
  unless scope.current > scope.outer do throw "higher-ranked universe is not fresh"
  pure ⟨#[], ← openPredicate clause.variables scope.current fuel clause.predicate⟩

/-- Every placeholder in an assigned value must be nameable in the universe
where the inference variable was created. This is a necessary assignment check,
not the region constraint collector's complete leak-check algorithm. -/
def checkAssignable (createdIn : Nat) : Nat → Term → Except String Unit
  | 0, _ => .error "higher-ranked placeholder visibility traversal exhausted"
  | fuel + 1, value => do
    match value with
    | .placeholder _ universeIndex .. =>
      unless universeIndex <= createdIn do throw "inference variable cannot name a higher universeIndex placeholder"
    | .node _ _ _ children | .definition _ _ _ children =>
      let _ ← children.mapM fun child => do
        checkAssignable createdIn fuel child
        pure child
      pure ()
    | .binder _ body => checkAssignable createdIn fuel body
    | _ => pure ()

end Miri.Input.TraitSelection.Universes
