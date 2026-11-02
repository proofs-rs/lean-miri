import duplicate_prefix.GeneralRangeMapOrigins
import duplicate_prefix.GeneralRangeMapState

namespace DuplicatePrefix
open Miri Miri.DataStructures

/-- Legacy allocation-wide versus window-local selected exposure contract.
The mode changes proof scope only; it does not change interpreter semantics. -/
inductive ProfileMode where
  | global
  | window
  deriving DecidableEq, Repr

namespace ProfileMode
/-- Global is definitionally the legacy Every predicate. Window requires only
stored segments intersecting the borrowed half-open interval. -/
abbrev Holds {α : Type} (mode : ProfileMode) (predicate : α → Prop)
    (lower upper : UInt64) (map : DedupRangeMap α) : Prop :=
  match mode with
  | .global => GeneralRangeMapState.Every predicate map
  | .window => GeneralRangeMapOrigins.OwnedOn predicate lower upper map

/-- Both supported modes supply precisely the window-local data required by
actual operation proofs. Nothing global is recovered from window mode. -/
theorem toOwned {α : Type} (mode : ProfileMode) (predicate : α → Prop)
    (lower upper : UInt64) (map : DedupRangeMap α)
    (facts : Holds mode predicate lower upper map) :
    GeneralRangeMapOrigins.OwnedOn predicate lower upper map := by
  cases mode with
  | global => intro position valid positive beforeUpper afterLower; exact facts position valid
  | window => exact facts

end ProfileMode
end DuplicatePrefix
