import duplicate_prefix.S04FinalReturn
import duplicate_prefix.PhysicalBoolReturn

namespace DuplicatePrefix.S04FinalReturnRuleScalar
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- The source scalar branch does not consult the scalar-pair padding policy. -/
theorem scalar_policy {K U : Type} [DecidableEq K]
    (access : PlaceMachine.AccessConfig K U) (place : MPlaceTy Provenance)
    (value : Scalar Provenance) (first second : MemoryOperandLayout → Bool) :
    PlaceMachine.writeMemory access first (.scalar value) place =
      PlaceMachine.writeMemory access second (.scalar value) place := by
  rfl

end DuplicatePrefix.S04FinalReturnRuleScalar
