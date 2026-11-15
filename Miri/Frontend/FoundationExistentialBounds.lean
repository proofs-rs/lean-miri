import Miri.Frontend.FoundationTypeRegistry

/-! Entailment of explicitly listed existential bounds only. Absence is an
Unsupported/unresolved query, never a negative trait answer: supertraits,
blanket impls, normalization and method/vtable resolution require more facts. -/
namespace Miri.Frontend.Foundation

private def sameArguments (a b : Array ConcreteType) : Bool :=
  a.size == b.size && (a.zip b).all (fun (x,y) => sameConcrete 1024 x y)

/-- Join a trait obligation with its exact explicit existential principal or
auto bound. Arguments exclude Self, just as in rustc's existential syntax. -/
def checkExplicitExistentialTrait (source : ExistentialType ConcreteType)
    (definition : Nat) (arguments : Array ConcreteType) : Except String Unit := do
  if source.principal == some definition && sameArguments source.arguments arguments then return ()
  if source.autoTraits.contains definition && arguments.isEmpty then return ()
  throw "dynamic trait bound not explicit; supertrait/impl resolution unsupported"

/-- Check an exact source equality, without resolving an associated type query
or assuming that a supertrait projection belongs directly to the principal. -/
def checkExplicitExistentialProjection (source : ExistentialType ConcreteType)
    (definition : Nat) (arguments : Array ConcreteType) (term : ConcreteType) : Except String Unit := do
  let candidates := source.projections.filter fun p =>
    p.definition == definition && sameArguments p.arguments arguments
  unless candidates.size == 1 do throw "existential projection equality missing or ambiguous"
  let some projection := candidates[0]? | throw "existential projection absent"
  unless sameConcrete 1024 projection.term term do throw "existential projection equality mismatch"

end Miri.Frontend.Foundation
