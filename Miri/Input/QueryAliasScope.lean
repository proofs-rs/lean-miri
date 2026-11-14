import Miri.Input.TraitSelection.HigherRankedMatch

/-! Alias argument ownership. Live placeholders are already
opened by the caller; lexical binders still need opening and reabstraction.
This does not normalize aliases or discharge their own predicates. -/
namespace Miri.Input.QueryAliasScope
open GenericSubstitution TraitSelection

private def noLexicalVariables : Nat → Term → Except String Unit
  | 0, _ => throw "query alias argument traversal exhausted"
  | fuel + 1, term => do
    match term with
    | .bound .. => throw "alias argument retains a lexical bound variable"
    | .parameter .. => throw "alias argument retains an early source parameter"
    | .inference .. => throw "alias argument retains an unresolved inference variable"
    | .binder _ body => noLexicalVariables fuel body
    | .node _ _ _ children | .definition _ _ _ children =>
      let _ ← children.mapM fun child => do noLexicalVariables fuel child; pure child
      pure ()
    | _ => pure ()

def requireOwned (maximumUniverse fuel : Nat) (argument : Term) : Except String Unit := do
  noLexicalVariables fuel argument
  HigherRankedMatch.requireScoped maximumUniverse fuel argument

end Miri.Input.QueryAliasScope
