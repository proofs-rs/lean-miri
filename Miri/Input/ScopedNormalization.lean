import Miri.Input.BinderRegions
import Miri.Input.TraitSelection.Match
import Miri.Input.QueryAliasScope

/-! Alias-free normalization inside quantified trait queries. Source binders
are region-only; placeholders of all sorts retain their query-owned identities.
Lexically bound alias arguments and deferred constants remain unsupported. -/
namespace Miri.Input.ScopedNormalization
open GenericSubstitution

/-- Alias parameters may contain already-opened query placeholders. Lexical
bound arguments still require binder-specific opening and reabstraction. -/
private def queryAliasDomain (maximumUniverse : Nat) : Nat → Term → Except String Unit
  | 0,_ => throw "scoped alias source-domain inspection exhausted"
  | fuel + 1,term => do
    match term with
    | .definition .type tag _ children =>
      if tag.startsWith "alias_" then
        let _ ← children.mapM fun child => do
          QueryAliasScope.requireOwned maximumUniverse fuel child
          pure child
        pure ()
      let _ ← children.mapM fun child => do queryAliasDomain maximumUniverse fuel child; pure child
      pure ()
    | .definition .constant tag _ _ =>
      if tag.startsWith "alias_" then throw "scoped constant alias requires const evaluation"
    | .node .constant tag _ children =>
      unless tag == "value" do throw "scoped normalization requires evaluated constants"
      let _ ← children.mapM fun child => do queryAliasDomain maximumUniverse fuel child; pure child
      pure ()
    | .binder _ body => queryAliasDomain maximumUniverse fuel body
    | .node _ _ _ children | .definition _ _ _ children =>
      let _ ← children.mapM fun child => do queryAliasDomain maximumUniverse fuel child; pure child
      pure ()
    | _ => pure ()

def prepareAliases (maximumUniverse fuel : Nat) (term : Term) : Except String Term := do
  TraitSelection.HigherRankedMatch.requireScoped maximumUniverse fuel term
  queryAliasDomain maximumUniverse fuel term
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
