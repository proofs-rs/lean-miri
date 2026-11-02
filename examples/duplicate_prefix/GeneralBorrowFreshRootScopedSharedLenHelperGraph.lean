import duplicate_prefix.GeneralBorrowFreshRootScopedSharedLenReleasedGraph
import duplicate_prefix.GeneralBorrowSharedFnEntryGlobalReturn
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometry
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedSharedLenHelperGraph
open Miri Miri.Interpreter Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Named actual helper tree. Kept irreducible at concrete callers to avoid
re-elaborating its interpreter loops while projecting graph-only resources. -/
def releasedTree (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (input : GeneralBorrowFreshRootScopedSharedFnEntry.Input tree tracker.global) : BorrowTree :=
  let borrowed := GeneralBorrowFreshRootScopedSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
  (borrowed.releaseProtector tracker.global.nextPointerTag held.global.protectedTags).tree

def endedGlobal (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) : GlobalState :=
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker room) tracker.global.nextPointerTag
  held.global.endCall (({} : FrameState).addProtector allocation tracker.global.nextPointerTag)

theorem releasedTree_eq (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (input : GeneralBorrowFreshRootScopedSharedFnEntry.Input tree tracker.global) :
    releasedTree tree tracker input =
      ((GeneralBorrowFreshRootScopedSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len).releaseProtector
        tracker.global.nextPointerTag
        (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag).global.protectedTags).tree := rfl

theorem endedGlobal_eq (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) :
    endedGlobal tracker allocation room =
      (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker room) tracker.global.nextPointerTag).global.endCall
        (({} : FrameState).addProtector allocation tracker.global.nextPointerTag) := rfl


/-- A proof-only graph/global ledger for the exact actual helper result. No
operation success or future-state premise is a field. This packaged API keeps
large caller expressions opaque during downstream Default/RootExit proofs. -/
structure HelperGraph (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (allocation : AllocId)
    (input : GeneralBorrowFreshRootScopedSharedFnEntry.Input tree tracker.global) : Prop where
  capacity : (releasedTree tree tracker input).locations.size = tree.locations.size
  well : (releasedTree tree tracker input).locations.WellFormed
  roots : (releasedTree tree tracker input).roots = tree.roots
  growth : (releasedTree tree tracker input).nodes.size ≤ tree.nodes.size+1
  short : (releasedTree tree tracker input).nodes.size < 65536
  distinct : (releasedTree tree tracker input).roots.toList.Nodup
  oldNodes : ∀ query oldNode, tree.nodeAt query = some oldNode →
    ∃ next, (releasedTree tree tracker input).nodeAt query = some next ∧ next.tag = oldNode.tag ∧
      next.parent = oldNode.parent ∧ next.isExposed = oldNode.isExposed
  oldTags : ∀ query oldNode, tree.nodeAt query = some oldNode →
    (releasedTree tree tracker input).indexOfTag oldNode.tag = some query
  table : (endedGlobal tracker allocation input.tagRoom).protectedTags = tracker.global.protectedTags
  get : ∀ query, (endedGlobal tracker allocation input.tagRoom).protectedTags.get query = tracker.global.protectedTags.get query
  contains : ∀ query, (endedGlobal tracker allocation input.tagRoom).protectedTags.contains query = tracker.global.protectedTags.contains query
  counter : (endedGlobal tracker allocation input.tagRoom).nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+1

section
/-- All packaged fields are derived once with abstract tree/tracker variables;
concrete callers need only apply this theorem and project the resulting record. -/
theorem package (tree : BorrowTree) (tracker : MachineHooks.BorrowState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree tracker.global)
    (input : GeneralBorrowFreshRootScopedSharedFnEntry.Input tree tracker.global) (stepRoom : tree.nodes.size+1 < 65536) :
    HelperGraph tree tracker allocation input := by
  let borrowed := GeneralBorrowFreshRootScopedSharedFnEntryArgument.finalTree tree tracker input.parentTag input.offset input.len
  let held := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker tracker input.tagRoom) tracker.global.nextPointerTag
  have frameExact : releasedTree tree tracker input = {borrowed with locations := (releasedTree tree tracker input).locations} :=
    GeneralBorrowStructuralReleaseGeometryFrame.release borrowed held.global.protectedTags tracker.global.nextPointerTag
  obtain ⟨borrowedRuntime,capacity,_,_,_⟩ := GeneralBorrowFreshRootScopedSharedFnEntryResources.resources tree tracker frame allocation runtime input
  have geometry := GeneralBorrowStructuralReleaseGeometry.release borrowed held.global.protectedTags tracker.global.nextPointerTag borrowedRuntime.formed.well
  obtain ⟨roots,growth,short,distinct,oldNodes⟩ := GeneralBorrowFreshRootScopedSharedLenReleasedGraph.ledger tree tracker frame allocation runtime input stepRoom
  have globalExact := GeneralBorrowSharedFnEntryGlobalReturn.global tree tracker.global runtime frame allocation input.tagRoom
  have globalReturn : endedGlobal tracker allocation input.tagRoom = GeneralBorrowFnEntryRegistration.advanced tracker.global input.tagRoom := globalExact
  refine ⟨geometry.2.trans capacity,geometry.1,roots,growth,short,distinct,oldNodes,?_,?_,?_,?_,?_⟩
  · intro query oldNode present
    obtain ⟨next,found,tag,_,_⟩ := oldNodes query oldNode present
    have originalFound : borrowed.nodeAt query = some next := by
      change (releasedTree tree tracker input).nodeAt query = some next at found
      rw [frameExact] at found
      exact found
    have mapped := borrowedRuntime.formed.allocator.nodeTags query next originalFound
    rw [frameExact]
    change borrowed.indexOfTag oldNode.tag = some query
    change borrowed.tagMapping.get oldNode.tag = some query
    rw [←tag]
    exact mapped
  · rw [globalReturn]
    rfl
  · intro query
    rw [globalReturn]
    rfl
  · intro query
    rw [globalReturn]
    rfl
  · rw [globalReturn]
    exact GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag input.tagRoom
end
attribute [irreducible] releasedTree endedGlobal
end DuplicatePrefix.GeneralBorrowFreshRootScopedSharedLenHelperGraph
