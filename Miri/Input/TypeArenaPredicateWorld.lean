import Miri.Input.GenericInstantiationWorld
import Miri.Input.BinderRegions

/-! Execution-owned existential predicate identities. The immutable material
prefix and the checked dense suffix share handles only within this World.
A constructed handle is not a material VtablePredicate index. -/
namespace Miri.Input.TypeArena

private def lift [Monad m] [MonadExceptOf String m] (value : Except String A) : m A :=
  match value with | .ok result => pure result | .error error => throw error

/-- Intern one complete closed region-only predicate after validating all child
identities and binder ownership. Unsupported syntax never creates a handle. -/
def World.internExistential (predicate : DynamicPredicate.Predicate) (fuel : Nat := 16384) :
    WorldM PredicateId := do
  let world ← get
  lift (world.validateExistential predicate)
  let term ← lift (DynamicPredicate.write (GenericInstantiationWorld.ofArgument world fuel) predicate)
  lift (BinderRegions.validateClosed #[] fuel term)
  World.internExistentialSyntax predicate

end Miri.Input.TypeArena
