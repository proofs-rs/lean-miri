import Miri.Input.BinderRegions
import Miri.Input.TraitSelection.Match

/-! Alias-free normalization inside quantified trait queries. Source binders
are region-only; placeholders of all sorts retain their query-owned identities.
This does not provide normalization of bound aliases or deferred constants. -/
namespace Miri.Input.ScopedNormalization
open GenericSubstitution

private def scopedVariable : Nat → Term → Except String Bool
  | 0,_ => throw "scoped alias argument inspection exhausted"
  | fuel + 1,term => do
    match term with
    | .bound .. | .placeholder .. | .parameter .. | .inference .. => pure true
    | .binder _ body => scopedVariable fuel body
    | .node _ _ _ children | .definition _ _ _ children => children.anyM (scopedVariable fuel)
    | _ => pure false

/-- The first scoped alias domain has closed arguments. Bound aliases need a
placeholder conversion tied to the binder's own obligations; ordinary tree
substitution is not a substitute for that operation. -/
private def closedAliasDomain : Nat → Term → Except String Unit
  | 0,_ => throw "scoped alias source-domain inspection exhausted"
  | fuel + 1,term => do
    match term with
    | .definition .type tag _ children =>
      if tag.startsWith "alias_" then
        if ← children.anyM (scopedVariable fuel) then
          throw "scoped alias arguments require higher-ranked placeholder conversion"
      let _ ← children.mapM fun child => do closedAliasDomain fuel child; pure child
      pure ()
    | .definition .constant tag _ _ =>
      if tag.startsWith "alias_" then throw "scoped constant alias requires const evaluation"
    | .node .constant tag _ children =>
      unless tag == "value" do throw "scoped normalization requires evaluated constants"
      let _ ← children.mapM fun child => do closedAliasDomain fuel child; pure child
      pure ()
    | .binder _ body => closedAliasDomain fuel body
    | .node _ _ _ children | .definition _ _ _ children =>
      let _ ← children.mapM fun child => do closedAliasDomain fuel child; pure child
      pure ()
    | _ => pure ()

def prepareAliases (maximumUniverse fuel : Nat) (term : Term) : Except String Term := do
  TraitSelection.HigherRankedMatch.requireScoped maximumUniverse fuel term
  closedAliasDomain fuel term
  BinderRegions.eraseAndAnonymizeScoped fuel term

def normalize (maximumUniverse fuel : Nat) (term : GenericSubstitution.Term) :
    Except String GenericSubstitution.Term := do
  TraitSelection.HigherRankedMatch.requireScoped maximumUniverse fuel term
  TraitSelection.HigherRankedMatch.requireNormalized fuel term
  BinderRegions.requireAliasFree fuel term
  let result ← BinderRegions.eraseAndAnonymizeScoped fuel term
  TraitSelection.HigherRankedMatch.requireScoped maximumUniverse fuel result
  pure result

end Miri.Input.ScopedNormalization
