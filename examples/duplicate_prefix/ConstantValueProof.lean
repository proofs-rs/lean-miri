import Miri.Interpreter.Constant
import Miri.TreeBorrows.TreeState

set_option maxRecDepth 4096
set_option maxHeartbeats 4000000

namespace DuplicatePrefix.ConstantValueProof
open Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.TreeBorrows

theorem scalar_zero (runtime : RuntimeMetadata)
    (queries : ConstantValueQueries Provenance BorrowTree K H)
    (state : ConstantState Provenance BorrowTree K H) (layout : LocalLayout) :
    valueToOpWithLayout runtime queries (.Scalar (.Int 0 8)) 5 (some layout) none state =
      .ok ⟨.immediate (.scalar (Scalar.fromScalarInt (ScalarInt.ofUInt64 0))), layout⟩ state := by
  with_unfolding_all rfl

#print axioms scalar_zero
end DuplicatePrefix.ConstantValueProof
