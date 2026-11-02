import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyScalarClean
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyCycleClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowExposedUniqueRootFamilySeed GeneralBorrowExposedUniqueRootFamilyAppend
open GeneralBorrowExposedUniqueRootFamilyRelease GeneralBorrowExposedUniqueRootFamilyCycle
open GeneralBorrowGcVacantClean GeneralBorrowFreshFutureClean GeneralRangeMapState RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Actual constructor/Write/release/exposure preserve every vacant permission
slot; no post-access cleanliness or successful-operation premise is used. -/
theorem cycle (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree) (roots : List UniIndex)
    (family : Family capacity global tree location roots) (allocation : AllocId)
    (fresh : global.nextPointerTag.value<18446744073709551615) (room : tree.nodes.size+1<65536)
    (clean : VacantClean tree) :
    VacantClean (finalTree capacity global tree location allocation fresh) := by
  obtain ⟨allocatedTag,readDone,builtExact,structural,locations,rootEq,present,stored,cache,old⟩ :=
    GeneralBorrowExposedUniqueRootFamilyAppend.append capacity global tree location roots family allocation fresh room
  have bounds : (0:UInt64).toNat+capacity.toNat≤tree.locations.size.bytes.toNat := by
    rw [family.locations]
    simp [homogeneous,DedupRangeMap.size,Size.ofBytes]
  have afterClean := GeneralBorrowPositiveWildcardVacantClean.preserves tree (mapping tree global) (index tree) global.nextPointerTag
    (.ReservedFrz false) .None GeneralBorrowFreshChild.inside 0 capacity family.structural.well bounds clean
  have finalNodes : (finalTree capacity global tree location allocation fresh).nodes=
      (after tree global capacity).nodes.insert (index tree)
        ({WildcardHitZeroConstructor.rootNode global.nextPointerTag (.ReservedFrz false) .None with isExposed:=true}:TreeNode) := by
    dsimp only [finalTree,GeneralBorrowExposeRead.marked,releaseTree]
  intro query vacant
  have different : query≠index tree := by
    intro same
    subst query
    rw [finalNodes,GeneralBorrowFreshLocation.get_same] at vacant
    cases vacant
  have oldVacant : (after tree global capacity).nodes.get query=none := by
    rw [finalNodes,GeneralBorrowFreshLocation.get_other (after tree global capacity).nodes (index tree) query
      ({WildcardHitZeroConstructor.rootNode global.nextPointerTag (.ReservedFrz false) .None with isExposed:=true}:TreeNode) different] at vacant
    exact vacant
  have storedClean : (locationAfter tree location).perms.get query=none := by
    have all := afterClean query oldVacant
    change Every (fun loc=>loc.perms.get query=none) (after tree global capacity).locations at all
    rw [locations] at all
    exact all 0 (by change 0<1;decide)
  have writeClean := GeneralBorrowExposedUniqueRootFamilyScalarClean.activate capacity global tree location roots family allocation fresh room query oldVacant storedClean
  have releaseClean := GeneralBorrowExposedUniqueRootFamilyScalarClean.release capacity global tree location roots family allocation fresh room query oldVacant writeClean
  change Every (fun loc=>loc.perms.get query=none)
    (homogeneous capacity (GeneralBorrowExposedUniqueRootFamilyCycle.finalLocation capacity global tree location allocation fresh))
  intro position valid
  have zero : position=0 := by change position<1 at valid;omega
  subst position
  change (GeneralBorrowExposedUniqueRootFamilyCycle.finalLocation capacity global tree location allocation fresh).perms.get query=none
  dsimp only [GeneralBorrowExposedUniqueRootFamilyCycle.finalLocation]
  exact releaseClean
end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyCycleClean
