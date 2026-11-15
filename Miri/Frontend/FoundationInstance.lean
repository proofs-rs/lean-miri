import Miri.Frontend.Foundation

/-! Explicit source arguments for startup signature substitution. Executable
instance/body demand belongs to the shared typed compiler World. -/
namespace Miri.Frontend.Foundation

inductive ItemArgument where
  | type (value : ConcreteType)
  | constant (value : Nat)
  deriving Repr


end Miri.Frontend.Foundation
