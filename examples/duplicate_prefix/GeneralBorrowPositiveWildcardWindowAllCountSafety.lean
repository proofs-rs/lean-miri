import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAllCountResult
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedSafety
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAllCountSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Exhaustive UInt64 count split for this raw sparse/mixed writable-leaf
wildcard contract: zero and rejected counts return physically, while positive
accepted counts perform the actual copy and return. Initial byte partitions,
lazy defaults and mixed effective writable leaves are retained. The fixed-MIR,
physical caller, leaf-forest and settings restrictions remain explicit; this
is not an arbitrary-caller or Rust-history formation theorem. -/
theorem invoke (s : GeneralBorrowPositiveWildcardWindowAllCountInput.Initial) :
    GeneralBorrowPositiveWildcardWindowAllCountResult.Result s.toBase := by
  by_cases zero : s.count=0
  · exact GeneralBorrowPositiveWildcardWindowAllCountResult.zero s zero
  · have positive : (0 : UInt64)<s.count:=UInt64.pos_iff_ne_zero.mpr zero
    by_cases within : s.count≤s.len/2
    · exact GeneralBorrowPositiveWildcardWindowAcceptedSafety.invoke
        (GeneralBorrowPositiveWildcardWindowAllCountInput.acceptedComplete s positive within)
    · have outside : s.count>s.len/2:=UInt64.lt_iff_toNat_lt.mpr
        (Nat.lt_of_not_ge (fun bound=>within (UInt64.le_iff_toNat_le.mpr bound)))
      exact GeneralBorrowPositiveWildcardWindowAllCountResult.rejected s outside
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAllCountSafety
