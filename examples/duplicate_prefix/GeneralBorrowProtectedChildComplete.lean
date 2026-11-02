import duplicate_prefix.GeneralBorrowProtectedChildOwnership
import duplicate_prefix.GeneralBorrowReleaseProperty
import duplicate_prefix.GeneralBorrowProtectedRootRead

namespace DuplicatePrefix.GeneralBorrowProtectedChildComplete
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralRangeMapState
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- From counterfactual unheld root data and exact real reservation typing,
actual protected child Write and actual release complete and recover a full
unheld root State. Actual endCall separately certifies that this unheld table is
the final real table; no registered root Write claim appears here. -/
theorem complete (tree : BorrowTree) (root child : UniIndex) (capacity : UInt64)
    (s : State tree root capacity) (node : TreeNode) (present : tree.nodeAt child = some node)
    (parent : node.parent = some root) (unexposed : node.isExposed = false)
    (tag : BorTag) (lookup : tree.indexOfTag tag = some child)
    (typed : GeneralBorrowDefaultReservationType.TreeTyped tree child)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree child .Write offset (offset+len))
    (global : GlobalState) (empty : global.protectedTags = {}) (allocation : AllocId) :
    let protections := (GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.protectedTags
    let written := GeneralBorrowProtectedMutableRelease.write tree tag offset len protections
    let released := GeneralBorrowProtectedMutableRelease.release tree tag offset len protections
    written.status = .Completed ∧ released.status = .Released ∧
    ((GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.endCall
      (GeneralBorrowProtectedMutableRelease.registration global allocation tag).2).protectedTags = {} ∧
    Nonempty {post : State released.tree root capacity // post.node.tag = s.node.tag} ∧
    released.tree.nodes = tree.nodes ∧ released.tree.tagMapping = tree.tagMapping := by
  dsimp only
  let protections := (GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.protectedTags
  let written := GeneralBorrowProtectedMutableRelease.write tree tag offset len protections
  let released := GeneralBorrowProtectedMutableRelease.release tree tag offset len protections
  have singleton : protections = ({} : ProtectedTags).insert tag .StrongProtector := by
    simp [protections,GeneralBorrowProtectedMutableRelease.registration,GlobalState.addProtector,empty]
  let depth := GeneralBorrowStarCertificates.depth tree root s.node s.star
  have children := GeneralBorrowStarCertificates.children tree root s.node s.star
  have covered := GeneralBorrowStarCertificates.covered tree root s.node s.star s.roots
  have fits : tree.nodes.data.size ≤ 4294967296 := by have bound := s.room;change tree.nodes.data.size+4 ≤ _ at bound;omega
  have allChildren : Every (GeneralBorrowRange.LocationOwned tree protections child .Write) tree.locations := by
    intro position valid
    have previous := s.owned position valid
    refine ⟨previous.1,?_⟩
    rw [singleton]
    exact GeneralBorrowProtectedChildOwnership.child tree _ root child s.node node s.star.present s.star.parentless present parent tag lookup
      s.allocator.nodeTags previous.2 (GeneralBorrowDefaultReservationType.effective tree _ child node present typed.1 (typed.2 position valid))
  have request : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat := by rw [s.capacity];exact bounds
  have facts := GeneralBorrowRangePreserves.ranged tree protections tag child root (Size.ofBytes offset) (Size.ofBytes len)
    .Write .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) fits depth children node present s.roots covered lookup s.well allChildren request
  let vacant := fun location : LocationTree => ∀ query, tree.nodes.get query = none → location.perms.get query = none
  have initialClean : Every vacant tree.locations := by intro position valid query missing;exact s.clean query missing position valid
  have cleanWrite := GeneralBorrowRangeProperty.preserves vacant tree protections tag child root (Size.ofBytes offset) (Size.ofBytes len)
    .Write .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) fits depth children node present s.roots covered lookup s.well allChildren initialClean (by
      intro location good owned query missing
      exact GeneralBorrowFreshActiveOnClean.normal_vacant tree location protections child query .Write .VisitChildrenOfAccessed
        depth children node present missing (good query missing)) request
  have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) .Write protections .VisitChildrenOfAccessed
  have writtenFrame : written.tree = {tree with locations := written.tree.locations} := frame
  have nodes : written.tree.nodes = tree.nodes := by simpa only [written,GeneralBorrowProtectedMutableRelease.write,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.nodes frame
  have mapping : written.tree.tagMapping = tree.tagMapping := by simpa only [written,GeneralBorrowProtectedMutableRelease.write,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.tagMapping frame
  have roots : written.tree.roots = tree.roots := by simpa only [written,GeneralBorrowProtectedMutableRelease.write,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.roots frame
  let nextDepth := GeneralBorrowFreshReadFrame.depth_on tree written.tree nodes depth
  have nextChildren : GeneralBorrowGraph.ChildNodes written.tree := by rw [writtenFrame];exact children
  have nextCovered : GeneralBorrowGraph.RootsCover written.tree := by rw [writtenFrame];exact covered
  have childPresent : written.tree.nodeAt child = some node := by change written.tree.nodes.get child = some node;rw [nodes];exact present
  have lookupAfter : written.tree.indexOfTag tag = some child := by change written.tree.tagMapping.get tag = some child;rw [mapping];exact lookup
  have nextFits : written.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact fits
  have activeAfter := GeneralBorrowFreshActiveWithinAccess.normal tree tag (Size.ofBytes offset) (Size.ofBytes len) .Write protections .VisitChildrenOfAccessed
    child offset (offset+len) s.well request (Nat.le_refl _) (Nat.le_refl _) active
  have localComplete := GeneralBorrowProtectedMutableRelease.write_release_restore tree global empty allocation tag child root node s.node present s.star.present
    parent s.star.parentless unexposed lookup depth children covered s.roots fits offset len nonzero s.well request active
    (by intro position valid positive lower upper;exact allChildren position valid)
  have sum : (offset+len).toNat = offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by
      change offset.toNat+len.toNat < 18446744073709551616
      have limit : capacity.toNat < 18446744073709551616 := UInt64.toNat_lt_size capacity
      omega)]
  have positive : offset.toNat < (offset+len).toNat := by
    have lenPositive : 0 < len.toNat := by
      have nz : len.toNat ≠ 0 := fun h => nonzero (UInt64.toNat_inj.mp (by simpa using h))
      omega
    rw [sum];omega
  let predicate := fun location : LocationTree => GeneralBorrowRange.LocationOwned written.tree protections child .Write location ∧ vacant location
  have initialProperty : Every predicate written.tree.locations := by
    intro position valid
    exact ⟨facts.2.1 position valid,cleanWrite.2.1 position valid⟩
  have scan := GeneralBorrowReleaseProperty.preserves written.tree protections tag child root .Write offset (offset+len) positive
    nextFits nextDepth nextChildren node childPresent unexposed (roots.trans s.roots) nextCovered lookupAfter
    (GeneralBorrowFreshActiveWithin.active_on written.tree child .Write offset (offset+len) facts.2.2.1 activeAfter)
    predicate initialProperty (by
      intro location range kind good owned kindRead
      refine ⟨GeneralBorrowRangePreserves.location_owned written.tree location protections child root kind .Write .SkipChildrenOfAccessed range kindRead
        nextFits owned nextDepth nextChildren node childPresent (roots.trans s.roots) nextCovered,?_⟩
      intro query missing
      obtain ⟨⟨forest⟩,owner⟩ := owned
      rw [GeneralBorrowRangePreserves.single_root_location written.tree location protections child root kind .SkipChildrenOfAccessed range forest
        (GeneralBorrowRangePreserves.owned_for_access _ child.toNat kind .Write kindRead owner)
        nextDepth nextChildren node childPresent (roots.trans s.roots) nextCovered]
      apply GeneralBorrowFreshActiveOnClean.normal_vacant written.tree location protections child query kind .SkipChildrenOfAccessed
        nextDepth nextChildren node childPresent
      · change written.tree.nodes.get query = none;rw [nodes];exact missing
      · exact good.2 query missing)
    (by intro position valid positive lower upper;exact facts.2.1 position valid)
  have releaseFrame : released.tree = {written.tree with locations := released.tree.locations} := scan.2.1
  have finalNodes : released.tree.nodes = tree.nodes := (congrArg BorrowTree.nodes releaseFrame).trans nodes
  have finalMapping : released.tree.tagMapping = tree.tagMapping := (congrArg BorrowTree.tagMapping releaseFrame).trans mapping
  have finalRoots : released.tree.roots = tree.roots := (congrArg BorrowTree.roots releaseFrame).trans roots
  have star := GeneralBorrowGeneratedStarShape.of_nodes tree released.tree root s.node finalNodes s.star
  have childFinal : released.tree.nodeAt child = some node := by change released.tree.nodes.get child = some node;rw [finalNodes];exact present
  have finalOwners : Every (GeneralBorrowRange.LocationOwned released.tree {} root .Write) released.tree.locations := by
    intro position valid
    have childOwned := (scan.2.2 position valid).1
    have actualChild : GeneralBorrowRange.LocationOwned released.tree protections child .Write released.tree.locations.entries[position].data := by
      have same : GeneralBorrowRange.LocationOwned released.tree protections child .Write = GeneralBorrowRange.LocationOwned written.tree protections child .Write := by
        funext location
        rw [releaseFrame,GeneralBorrowFreshInstallation.location_map]
      rw [same]
      exact childOwned
    have unheld := GeneralBorrowFreshProtectorRelease.location_weakens released.tree _ protections {} (by intro tag impossible;simp [ProtectedTags.contains,ProtectedTags.get] at impossible) child .Write actualChild
    exact ⟨unheld.1,GeneralBorrowRootChildWriteOwnership.root_of_child released.tree _ root child s.node node star.present star.parentless childFinal parent unheld.2⟩
  have finalClean : GeneralBorrowGcVacantClean.VacantClean released.tree := by
    intro query missing position valid
    rw [finalNodes] at missing
    exact (scan.2.2 position valid).2 query missing
  refine ⟨facts.1,scan.1,GeneralBorrowProtectedMutableRelease.end_call_empty global empty allocation tag,
    ⟨⟨⟨s.node,s.nonzero,star,finalRoots.trans s.roots,localComplete.2.2.2.2.2.trans s.capacity,
      localComplete.2.2.2.2.1,finalOwners,?_,finalClean,?_⟩,rfl⟩⟩,finalNodes,finalMapping⟩
  · constructor
    · rw [finalNodes,finalMapping];exact s.allocator.pool
    · unfold GeneralBorrowFreshStagePool.Accounting;rw [finalNodes,finalMapping];exact s.allocator.accounting
    · rw [finalMapping];exact s.allocator.unique
    · intro query value found
      rw [finalNodes] at found
      rw [finalMapping]
      exact s.allocator.nodeTags query value found
  · rw [finalNodes];exact s.room
end
end DuplicatePrefix.GeneralBorrowProtectedChildComplete
