import duplicate_prefix.GeneralBorrowSparseExposedRootHistory
namespace DuplicatePrefix.GeneralBorrowSparseExposedRootAccessHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSparseExposedRootFormation GeneralBorrowSparseExposedRootHistory GeneralBorrowSparseExposedLeafState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def formed (capacity : UInt64) (nonzero : capacity≠0) (windows : List (Window capacity)) (room : windows.length+2<65536) :=
  generate (seeded capacity nonzero) windows (by change 1+windows.length<65536;omega)
    (by change 2+windows.length<65536;omega)

/-- One actual source sequence forms mixed explicit/lazy permissions through
partial root constructors/exposures, then executes any bounded ranged NONE
Read/Write suffix. Every source tag, cache/cardinality, partition, ownership and
completion is produced internally from root allocation and numeric windows.
No whole-MIR FnEntry, unrestricted interleaving or all-valid-caller claim follows. -/
theorem executes (capacity : UInt64) (nonzero : capacity≠0) (windows : List (Window capacity)) (room : windows.length+2<65536)
    (events : List (GeneralBorrowSparseExposedLeafHistory.Event capacity)) :
    let built:=(formed capacity nonzero windows room).state
    let before:=GeneralBorrowSparseExposedRootHistory.State.toAccess built
    let after:=GeneralBorrowSparseExposedLeafHistory.run before events
    GlobalState.new.rootPointerTag GeneralBorrowProtectedLifetimeSeed.allocation=
      .ok (GeneralBorrowProtectedLifetimeSeed.global,BorTag.one) ∧
    (BorrowTree.new BorTag.one (Size.ofBytes capacity)).exposeTag GeneralBorrowProtectedLifetimeSeed.global.protectedTags BorTag.one=
      ⟨(seeded capacity nonzero).tree,.ok ()⟩ ∧
    GeneralBorrowSparseExposedRootHistory.Trace (seeded capacity nonzero) windows built ∧
    GeneralBorrowSparseExposedLeafHistory.Trace before events after ∧
    GeneralRangeMapOrigins.OwnedOn (fun location=>Raw after.tree location built.global.protectedTags) 0 capacity after.tree.locations ∧
    after.tree.locations.WellFormed ∧ after.tree.locations.size=Size.ofBytes capacity := by
  have source:=GeneralBorrowSparseExposedRootHistory.from_seed capacity nonzero windows room
  exact ⟨source.1,source.2.1,source.2.2,GeneralBorrowSparseExposedLeafHistory.run_trace _ events,by exact (GeneralBorrowSparseExposedLeafHistory.run _ events).raw,
    (GeneralBorrowSparseExposedLeafHistory.run _ events).well,(GeneralBorrowSparseExposedLeafHistory.run _ events).capacityEq⟩
end
end DuplicatePrefix.GeneralBorrowSparseExposedRootAccessHistory
