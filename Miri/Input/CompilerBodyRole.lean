/-! Source MIR roles select different pinned compiler bodies for the same
physical instance. CTFE Item bodies use mir_for_ctfe; ordinary runtime bodies
use instance_mir. The role is part of body identity, not display metadata. -/
namespace Miri.Input
inductive CompilerBodyRole where
  | runtime
  | ctfe
  deriving Repr, DecidableEq, BEq
end Miri.Input
