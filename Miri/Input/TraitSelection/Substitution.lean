import Miri.Input.TraitSelection.Material

/-! Early substitution into raw trait clauses. A clause is a rustc Binder:
substituting each embedded term under that binder preserves shifts of escaping
bound variables. This does not solve clauses or erase their bound variables. -/
namespace Miri.Input.TraitSelection.Substitution
open GenericSubstitution

private def underBinder (fuel : Nat) (arguments : Array Term)
    (variables : Array BoundVariable) (term : Term) : Except String Term := do
  let value ← GenericSubstitution.instantiate fuel arguments (.binder variables term)
  let .binder actual value := value | throw "trait clause substitution lost binder"
  unless actual == variables do throw "trait clause substitution changed bound variables"
  pure value

def predicate (fuel : Nat) (arguments : Array Term) (variables : Array BoundVariable)
    (value : Predicate) : Except String Predicate := do
  let term := underBinder fuel arguments variables
  match value with
  | .trait goal =>
    return .trait {goal with traitRef := {goal.traitRef with
      arguments := ← goal.traitRef.arguments.mapM term}}
  | .hostEffect requiresConst traitRef =>
    return .hostEffect requiresConst {traitRef with arguments := ← traitRef.arguments.mapM term}
  | .unstableFeature feature => pure (.unstableFeature feature)
  | .equal left right => return .equal (← term left) (← term right)
  | .projection kind associated values expected =>
    return .projection kind associated (← values.mapM term) (← term expected)
  | .regionOutlives longer shorter => return .regionOutlives (← term longer) (← term shorter)
  | .typeOutlives ty region => return .typeOutlives (← term ty) (← term region)
  | .constEvaluatable value => return .constEvaluatable (← term value)
  | .constHasType value ty => return .constHasType (← term value) (← term ty)
  | .wellFormed value => return .wellFormed (← term value)

def clause (fuel : Nat) (arguments : Array Term) (value : Clause) : Except String Clause := do
  return {value with predicate := ← predicate fuel arguments value.variables value.predicate}

def clauses (fuel : Nat) (arguments : Array Term) (values : Array Clause) :
    Except String (Array Clause) :=
  values.mapM (clause fuel arguments)

end Miri.Input.TraitSelection.Substitution
