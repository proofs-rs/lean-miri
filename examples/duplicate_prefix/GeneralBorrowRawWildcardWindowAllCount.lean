import duplicate_prefix.GeneralBorrowRawWildcardWindowAcceptedReturn
import duplicate_prefix.GeneralBorrowRawWildcardWindowRejectedReturn
import duplicate_prefix.GeneralBorrowRawWildcardWindowZeroOutcome
namespace DuplicatePrefix.GeneralBorrowRawWildcardWindowAllCount
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext GeneralBorrowRawWildcardWindowInitial
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
/-- One original wildcard call and its actual return, for every UInt64 count
under a count-independent positive live-hit contract. Exact-base and interior
windows are included. This is conditional NoUB, not all-valid-input coverage;
Initial and the explicit hypotheses retain configuration, metadata, resources,
physical storage and semantic borrow-authorization restrictions. -/
theorem invoke (s : Initial)
    (preciseOff : s.options.retag.preciseInteriorMut = false)
    (implicitOff : s.options.retag.implicitWrites = false)
    (budget : Nat) (dispatch : s.limits.callDispatch = budget+1)
    (nodeMargin : s.entry.allocation.extra.nodes.size+5 < 65536)
    (tagMargin : s.tracker.global.nextPointerTag.value.toNat+5 < 18446744073709551615)
    (bytes : GeneralBorrowRawSliceBytes.Data s.entry.allocation (offset s) s.len)
    (bufferExtras : s.before.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == s.id) = some (s.id,⟨none,#[]⟩))
    (statementFuel : s.limits.validation = s.validityFuel+1) (n : UInt64) :
    DuplicatePrefixArgumentCallResult.Result s.options s.limits s.remaining s.span s.before
      (.pointer (Pointer.new .wildcard (Size.ofBytes s.address))) s.len n s.place := by
  by_cases zero : n = 0
  · subst n
    obtain ⟨outcome⟩ := GeneralBorrowRawWildcardWindowZeroOutcome.invoke s
    exact outcome.safety
  by_cases within : n ≤ s.len/2
  · exact GeneralBorrowRawWildcardWindowAcceptedReturn.invoke s n zero within preciseOff implicitOff budget dispatch nodeMargin tagMargin bytes bufferExtras statementFuel
  · exact GeneralBorrowRawWildcardWindowRejectedReturn.invoke s n zero (UInt64.not_le.mp within) preciseOff implicitOff budget dispatch (by omega) (by omega)
end
end DuplicatePrefix.GeneralBorrowRawWildcardWindowAllCount
