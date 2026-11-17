import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAllCountInput
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAllCountResult
open Miri Miri.ABI Miri.Memory
variable [area : GeneralBorrowExposedKnownRootState.Scope]
variable {profileMode : ProfileMode}
noncomputable section
/-- The common public call-time result, with the original concrete provenance
and actual interior pointer. This definition imposes no validity classification. -/
abbrev Result (s : GeneralBorrowPositiveConcreteWindowOriginalInput.BaseFor profileMode) : Prop :=
  DuplicatePrefixCallResult.Result s.options s.limits s.remaining s.span s.before
    (Pointer.new (.concrete s.id s.parentTag) (Size.ofBytes (s.base+s.offset))) s.len s.count s.place

theorem zero (s : GeneralBorrowPositiveConcreteWindowAllCountInput.InitialFor profileMode) (zero : s.count=0) : Result s.toBase :=
  GeneralBorrowPositiveConcreteWindowEarlyCallResult.zero (GeneralBorrowPositiveConcreteWindowAllCountInput.zero s zero)

theorem rejected (s : GeneralBorrowPositiveConcreteWindowAllCountInput.InitialFor profileMode) (outside : s.count>s.len/2) : Result s.toBase :=
  GeneralBorrowPositiveConcreteWindowEarlyCallResult.rejected (GeneralBorrowPositiveConcreteWindowAllCountInput.rejected s outside)
end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAllCountResult
