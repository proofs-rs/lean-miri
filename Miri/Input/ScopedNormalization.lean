import Miri.Input.BinderRegions
import Miri.Input.TraitSelection.Match

/-! Alias-free normalization inside quantified trait queries. Source binders
are region-only; placeholders of all sorts retain their query-owned identities.
This does not provide normalization of bound aliases or deferred constants. -/
namespace Miri.Input.ScopedNormalization

def normalize (maximumUniverse fuel : Nat) (term : GenericSubstitution.Term) :
    Except String GenericSubstitution.Term := do
  TraitSelection.HigherRankedMatch.requireScoped maximumUniverse fuel term
  TraitSelection.HigherRankedMatch.requireNormalized fuel term
  BinderRegions.requireAliasFree fuel term
  let result ← BinderRegions.eraseAndAnonymizeScoped fuel term
  TraitSelection.HigherRankedMatch.requireScoped maximumUniverse fuel result
  pure result

end Miri.Input.ScopedNormalization
