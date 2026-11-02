import duplicate_prefix.GeneralBorrowPositiveWildcardFamilyAllCount
import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyGenerated
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardGeneratedFamilySafety
open Miri Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowPositiveWildcardFamilyPhysical
open GeneralBorrowExposedUniqueRootFamilyGenerated
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
noncomputable section
/-- Initial root allocation/exposure and real source history generate every
borrow, cache, allocator and vacancy premise for the original all-count call.
The caller supplies physical memory, compiler/settings data and numeric room;
no final borrow row, coherent cache, successful operation or Family is assumed.
This is a SourceModel-history connection, not Rust-history reachability. -/
theorem invoke (cycles : Nat) (capacity : UInt64) (nonzero : capacity≠0)
    (nodeRoom : 1+cycles<65536) (tagRoom : 2+cycles≤18446744073709551615)
    (p : Caller capacity (build cycles capacity nonzero nodeRoom tagRoom).global
      (build cycles capacity nonzero nodeRoom tagRoom).tree)
    (sameAllocation : p.id=GeneralBorrowProtectedLifetimeSeed.allocation) :
    let generated:=build cycles capacity nonzero nodeRoom tagRoom
    GlobalState.new.rootPointerTag p.id=.ok (GeneralBorrowProtectedLifetimeSeed.global,BorTag.one) ∧
    (BorrowTree.new BorTag.one (Size.ofBytes capacity)).exposeTag
      GeneralBorrowProtectedLifetimeSeed.global.protectedTags BorTag.one=
      ⟨GeneralBorrowRootExposureSeed.exposedTree capacity BorTag.one,.ok ()⟩ ∧
    GeneralBorrowExposedUniqueRootFamilyHistory.History capacity p.id cycles
      GeneralBorrowProtectedLifetimeSeed.global (GeneralBorrowRootExposureSeed.exposedTree capacity BorTag.one)
      GeneralBorrowRootExposureSeed.exposedLocation [GeneralBorrowRootExposureSeed.root]
      generated.global generated.tree generated.location generated.roots ∧
    @GeneralBorrowPositiveWildcardAllCountResult.Result (scope generated.roots)
      (GeneralBorrowPositiveWildcardFamilyInput.base p generated.family) := by
  let generated:=build cycles capacity nonzero nodeRoom tagRoom
  refine ⟨?_,generated.exposed,?_,?_⟩
  · rw [sameAllocation]
    exact generated.allocated
  · rw [sameAllocation]
    exact generated.history
  · exact GeneralBorrowPositiveWildcardFamilyAllCount.invoke p generated.family generated.vacantClean
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardGeneratedFamilySafety
