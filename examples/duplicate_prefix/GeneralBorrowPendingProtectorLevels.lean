import duplicate_prefix.GeneralBorrowExposureAncestorFold
namespace DuplicatePrefix.GeneralBorrowPendingProtectorLevels
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowExposureAncestorFold

/-- A raw ForeignRead while the source global table still holds protection
conflicts an unconflicted reservation. In the virtual table with that tag
already removed, both permission endpoints instead support local Write.
This is a local permission calculation, not a reachable-history counterexample. -/
theorem reservation_read :
    performAccessTransition .Read .ForeignAccess (.ReservedFrz false) true =
      .Transition ⟨.ReservedFrz false,.ReservedFrz true⟩ ∧
    Permission.strongestAllowedLocalAccess (.ReservedFrz false) true = .Write ∧
    Permission.strongestAllowedLocalAccess (.ReservedFrz true) true = .Read ∧
    Permission.strongestAllowedLocalAccess (.ReservedFrz false) false = .Write ∧
    Permission.strongestAllowedLocalAccess (.ReservedFrz true) false = .Write := by
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

/-- The source counter delta in that raw transition differs from the delta
computed with the already-removed virtual table. A bulk release invariant must
account for this case or derive its exclusion from actual-history metadata. -/
theorem reservation_write_deltas (value : UInt16) :
    delta value
      (supportsWrite (Permission.strongestAllowedLocalAccess (.ReservedFrz false) true))
      (supportsWrite (Permission.strongestAllowedLocalAccess (.ReservedFrz true) true)) = value-1 ∧
    delta value
      (supportsWrite (Permission.strongestAllowedLocalAccess (.ReservedFrz false) false))
      (supportsWrite (Permission.strongestAllowedLocalAccess (.ReservedFrz true) false)) = value := by
  exact ⟨rfl,rfl⟩

/-- A finite arithmetic witness to the difference above. This theorem says
nothing about reachability, operation completion or the duplicate_prefix call. -/
theorem one_write_deltas_differ :
    delta (1 : UInt16) (supportsWrite .Write) (supportsWrite .Read) ≠
      delta (1 : UInt16) (supportsWrite .Write) (supportsWrite .Write) := by
  decide

end DuplicatePrefix.GeneralBorrowPendingProtectorLevels
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowPendingProtectorLevels.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved pending-protector level dependency {dependency}"
