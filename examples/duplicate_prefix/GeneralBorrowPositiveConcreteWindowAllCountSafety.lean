import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAllCountResult
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedSafety
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAllCountSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
variable [area : GeneralBorrowExposedKnownRootState.Scope]
variable {profileMode : ProfileMode}
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Exhaustive count split for the explicit sufficient call-time contract.
No source-history or complete-valid-caller coverage theorem is claimed. -/
theorem invoke (s : GeneralBorrowPositiveConcreteWindowAllCountInput.InitialFor profileMode) :
    GeneralBorrowPositiveConcreteWindowAllCountResult.Result s.toBase := by
  by_cases zero : s.count=0
  · exact GeneralBorrowPositiveConcreteWindowAllCountResult.zero s zero
  · have positive : (0 : UInt64)<s.count:=UInt64.pos_iff_ne_zero.mpr zero
    by_cases within : s.count≤s.len/2
    · exact GeneralBorrowPositiveConcreteWindowAcceptedSafety.invoke
        (GeneralBorrowPositiveConcreteWindowAllCountInput.acceptedComplete s positive within)
    · have outside : s.count>s.len/2:=UInt64.lt_iff_toNat_lt.mpr
        (Nat.lt_of_not_ge (fun bound=>within (UInt64.le_iff_toNat_le.mpr bound)))
      exact GeneralBorrowPositiveConcreteWindowAllCountResult.rejected s outside
end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAllCountSafety
