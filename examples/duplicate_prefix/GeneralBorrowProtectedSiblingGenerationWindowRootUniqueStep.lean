import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowAdvance
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationWindowRootUniqueRead
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowRootUniqueStep
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralRangeMapOrigins GeneralBorrowProtectedSiblingGenerationWindowCore
open GeneralBorrowConstructorPriorPermission
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem preserves {capacity remaining selected future} (before : Core capacity remaining)
    (step : GeneralBorrowProtectedSiblingGenerationStep.Ready before.input before.global before.frame GeneralBorrowProtectedSiblingGenerationWindowSeed.allocation selected future)
    (initial : Every (At before.input.parent (some .Unique)) before.input.tree.locations) :
    Every (At step.next.parent (some .Unique)) step.next.tree.locations := by
  have owned := GeneralBorrowProtectedSiblingGenerationWindowRootUniqueRead.child before.input step.output.global.protectedTags
    before.roots step.registeredProfile step.prepared initial
  have well := (GeneralBorrowFreshMutableGeometry.append_frame step.prepared.next).1
  have geometry := GeneralBorrowFreshGeometry.shape_frame _ _ step.shape well
  have size : (GeneralBorrowFreshMetadataChildMutable.result step.prepared.next).locations.size = Size.ofBytes capacity :=
    geometry.2.symm.trans (step.capacity.trans before.capacity)
  have all : Every (At before.input.parent (some .Unique)) (GeneralBorrowFreshMetadataChildMutable.result step.prepared.next).locations := by
    refine GeneralBorrowTwoProtectedStateInfoFullRange.every _ (At before.input.parent (some .Unique)) capacity well size ?_
    rw [step.prepared.result]
    simpa only [before.offset,before.len,UInt64.zero_add] using owned
  rw [step.parent]
  exact GeneralBorrowConstructorPriorPermission.shape _ _ step.shape before.input.parent (some .Unique) all
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowRootUniqueStep
