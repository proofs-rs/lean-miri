import duplicate_prefix.GeneralBorrowStructuralHistoryActivityFull
import duplicate_prefix.GeneralBorrowWildcardRootInstalled
namespace DuplicatePrefix.GeneralBorrowScopedDefaultReleaseActivity
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralBorrowFreshReleaseLoop
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Full positive Default reservation materialization derives the exact Read
callback kind and activity for the original wildcard FnEntry root. The final
release's success and any callback are absent from these source-state facts. -/
theorem formed (tree : BorrowTree) (index : UniIndex) (capacity : UInt64)
    (positive : (0:UInt64).toNat<capacity.toNat) (well : tree.locations.WellFormed)
    (size : tree.locations.size.bytes=capacity)
    (installed : OwnedOn (fun location : LocationTree=>location.perms.get index=some GeneralBorrowFreshChild.inside)
      0 capacity tree.locations) :
    ActiveOn tree index .Read 0 capacity ∧
    (∀ position (valid : position<tree.locations.entries.size) state,
      tree.locations.entries[position].data.perms.get index=some state → state.accessed=true →
      ∀ kind,state.permission.associatedAccess=some kind → kind=.Read) := by
  have full := GeneralBorrowFreshActiveWithin.active_on tree index .Write 0 tree.locations.size.bytes well
    (GeneralBorrowStructuralHistoryActivityFull.full tree index well)
  rw [size] at full
  have matching : ∀ position (valid : position<tree.locations.entries.size) state,
      tree.locations.entries[position].data.perms.get index=some state → state.accessed=true →
      ∀ kind,state.permission.associatedAccess=some kind → kind=.Read := by
    intro position valid state stored accessed kind associated
    have overlap := full position valid state stored accessed kind associated
    have expected := installed position valid positive overlap.1 overlap.2.1
    have same := Option.some.inj (stored.symm.trans expected)
    subst state
    simpa only [GeneralBorrowFreshChild.inside,Permission.associatedAccess,Option.some.injEq] using associated.symm
  refine ⟨?_,matching⟩
  intro position valid state stored accessed kind associated
  exact ⟨(full position valid state stored accessed kind associated).1,
    (full position valid state stored accessed kind associated).2.1,fun _=>matching position valid state stored accessed kind associated⟩
end DuplicatePrefix.GeneralBorrowScopedDefaultReleaseActivity
