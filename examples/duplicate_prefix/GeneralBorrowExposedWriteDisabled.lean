import duplicate_prefix.GeneralBorrowGeneratedExposedWrite
import duplicate_prefix.GeneralBorrowFrozenStarWriteStored
import duplicate_prefix.GeneralBorrowNormalStoredWriteback
namespace DuplicatePrefix.GeneralBorrowExposedWriteDisabled
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowExposedProtocolWrite
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposureHistoryBounds
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- The actual full-range Write stores Disabled at every exposed nonroot node;
its exact resulting cache and unchanged exposed flags belong to the same tree. -/
theorem write (input : Input) (s : GeneralBorrowExposedStarFormation.Output input) :
    ∃ postLocation, (operation input s).tree.locations = RangeMapNonempty.homogeneous input.len postLocation ∧
      reads postLocation.exposedCache input.parent = 1 ∧ writes postLocation.exposedCache input.parent = 1 ∧
      (∀ query,query ≠ input.parent → reads postLocation.exposedCache query = 0 ∧ writes postLocation.exposedCache query = 0) ∧
      ∀ index node,(operation input s).tree.nodeAt index = some node → index ≠ input.parent →
        ∃ state,postLocation.perms.get index = some state ∧ state.permission = .Disabled := by
  have fits : s.tree.nodes.size ≤ 4294967296 := by have bound := s.state.room;omega
  obtain ⟨⟨forest⟩,owned⟩ := GeneralBorrowStarOwnership.location_owned s.tree input.parent s.node s.star s.location s.profile fits
  have tagged := s.state.allocator.nodeTags input.parent s.state.node s.state.star.present
  have full := GeneralBorrowHomogeneousFullAccess.full s.tree input.parent s.node s.state.node.tag input.len input.nonzero s.location .Write
    tagged s.locations s.star s.state.roots forest owned
  have counted := GeneralBorrowExposedStarWrite.normal s.tree s.location input.parent s.node s.star s.profile fits s.exposed s.counts
  refine ⟨(s.tree.performNormalAccessAt s.location input.parent .Write {} .VisitChildrenOfAccessed).location,?_,counted.2.1,counted.2.2.1,counted.2.2.2,?_⟩
  · exact congrArg BorrowTree.locations full.2
  · intro index node present different
    change (operation input s).tree.nodeAt index = some node at present
    rw [show (operation input s).tree = _ from full.2] at present
    obtain ⟨state,stored,disabled⟩ := GeneralBorrowFrozenStarWriteStored.normal_disabled s.tree s.location input.parent s.node
      s.star s.profile fits s.exposed index node present different
    exact ⟨state,GeneralBorrowNormalStoredWriteback.stored s.tree s.location {} input.parent index .Write .VisitChildrenOfAccessed state stored,disabled⟩

/-- Allocation-to-exposure-to-Write guarantee: no initial State, cache, Ready,
profile, event metadata or successful-operation premise is supplied. -/
theorem generate (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag)
    (different : rootTag ≠ childTag) (tags : List BorTag) (distinct : tags.Nodup)
    (rootUnused : rootTag ∉ tags) (childUnused : childTag ∉ tags) (short : 2+tags.length < 65536) :
    let seed := GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different
    ∃ (final : Input) (exposed : GeneralBorrowExposedStarFormation.Output final) (postLocation : LocationTree),
      GeneralBorrowFullSharedRepeat.Run seed tags final ∧
      (operation final exposed).status = .Completed ∧
      Nonempty (GeneralBorrowPartitionState.State (operation final exposed).tree final.parent final.len) ∧
      (∀ index node,(operation final exposed).tree.nodeAt index = some node → node.isExposed = true) ∧
      (operation final exposed).tree.locations = RangeMapNonempty.homogeneous capacity postLocation ∧
      reads postLocation.exposedCache final.parent = 1 ∧ writes postLocation.exposedCache final.parent = 1 ∧
      (∀ query,query ≠ final.parent → reads postLocation.exposedCache query = 0 ∧ writes postLocation.exposedCache query = 0) ∧
      ∀ index node,(operation final exposed).tree.nodeAt index = some node → index ≠ final.parent →
        ∃ state,postLocation.perms.get index = some state ∧ state.permission = .Disabled := by
  obtain ⟨final,exposed,history,complete,state,flags,ignored,ignoredLocations,ignoredCounts⟩ :=
    GeneralBorrowGeneratedExposedWrite.generate capacity nonzero rootTag childTag different tags distinct rootUnused childUnused short
  obtain ⟨postLocation,locations,counted⟩ := write final exposed
  have length : final.len = capacity := history.length
  refine ⟨final,exposed,postLocation,history,complete,state,flags,?_,counted⟩
  rw [←length]
  exact locations
end DuplicatePrefix.GeneralBorrowExposedWriteDisabled
