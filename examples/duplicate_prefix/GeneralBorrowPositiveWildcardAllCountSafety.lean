import duplicate_prefix.GeneralBorrowPositiveWildcardAllCountResult
import duplicate_prefix.GeneralBorrowPositiveWildcardAcceptedSafety
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardAllCountSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Every UInt64 count in one restricted exact-base positive wildcard family:
zero returns physically, a positive accepted count executes real copy and return,
and a rejected count executes real false return. Every branch starts from the
same raw OriginalInput.Base caller and internally forms its intermediate data.
This does not cover arbitrary valid callers, mixed partitions or nonleaf exposed
forests; the homogeneous exposed-Unique-leaf and explicit initial resource,
compiler/physical/settings conditions remain part of the contract. -/
theorem invoke (s : GeneralBorrowPositiveWildcardAllCountInput.Initial) :
    GeneralBorrowPositiveWildcardAllCountResult.Result s.toBase := by
  by_cases zero : s.count=0
  · exact GeneralBorrowPositiveWildcardAllCountResult.zero s zero
  · have positive : (0 : UInt64)<s.count:=UInt64.pos_iff_ne_zero.mpr zero
    by_cases within : s.count≤s.len/2
    · let input : GeneralBorrowPositiveWildcardAcceptedCompleteInput.Initial:={
        toAccepted:=GeneralBorrowPositiveWildcardAllCountInput.accepted s positive within,
        statementFuel:=s.statementFuel }
      exact GeneralBorrowPositiveWildcardAcceptedSafety.invoke input
    · have outside : s.count>s.len/2:=UInt64.lt_iff_toNat_lt.mpr
        (Nat.lt_of_not_ge (fun bound=>within (UInt64.le_iff_toNat_le.mpr bound)))
      exact GeneralBorrowPositiveWildcardAllCountResult.rejected s outside
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardAllCountSafety
