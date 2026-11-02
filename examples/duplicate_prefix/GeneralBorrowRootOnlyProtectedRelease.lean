import duplicate_prefix.GeneralBorrowRootOnlyProtectedChildCache
import duplicate_prefix.GeneralBorrowProtectedChildComplete

namespace DuplicatePrefix.GeneralBorrowRootOnlyProtectedRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowRootOnlyExposureExact DuplicatePrefix.GeneralBorrowRootOnlyRangeCache
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.GeneralRangeMapOrigins DuplicatePrefix.GeneralBorrowPartitionState
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Protected child Write and the real protector-end access preserve the
original exposed root's Unique storage, exact cache and flag. The pre-Write
root State is explicitly counterfactual under {}; actual child ownership under
the registration is derived, and registered root Write is never claimed. -/
theorem frame (tree : BorrowTree) (root child : UniIndex) (capacity : UInt64) (s : State tree root capacity)
    (node : TreeNode) (present : tree.nodeAt child = some node) (parent : node.parent = some root)
    (unexposed : node.isExposed = false) (tag : BorTag) (lookup : tree.indexOfTag tag = some child)
    (typed : GeneralBorrowDefaultReservationType.TreeTyped tree child)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (active : GeneralBorrowFreshActiveWithin.ActiveWithin tree child .Write offset (offset+len))
    (global : GlobalState) (empty : global.protectedTags = {}) (allocation : AllocId)
    (cache : ExposedCache) (only : RootOnly tree root) (initial : Every (LocationInvariant cache root) tree.locations) :
    let protections := (GeneralBorrowProtectedMutableRelease.registration global allocation tag).1.protectedTags
    let after := (GeneralBorrowProtectedMutableRelease.release tree tag offset len protections).tree
    RootOnly after root ∧ Every (LocationInvariant cache root) after.locations ∧
      (after.nodes.get root).map TreeNode.isExposed = (tree.nodes.get root).map TreeNode.isExposed := by
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
  have writtenInvariant := GeneralBorrowRootOnlyProtectedChildCache.ranged tree root child capacity s node present parent tag lookup
    offset len bounds .Write protections only cache initial allChildren
  have facts := GeneralBorrowRangePreserves.ranged tree protections tag child root (Size.ofBytes offset) (Size.ofBytes len)
    .Write .Write .VisitChildrenOfAccessed (by intro impossible;cases impossible) fits depth children node present s.roots covered lookup s.well allChildren request
  have firstFrame := GeneralBorrowFreshReadFrame.frame tree (.concrete tag) (Size.ofBytes offset) (Size.ofBytes len) .Write protections .VisitChildrenOfAccessed
  have writtenFrame : written.tree = {tree with locations := written.tree.locations} := firstFrame
  have nodes : written.tree.nodes = tree.nodes := by simpa only [written,GeneralBorrowProtectedMutableRelease.write,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.nodes firstFrame
  have mapping : written.tree.tagMapping = tree.tagMapping := by simpa only [written,GeneralBorrowProtectedMutableRelease.write,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.tagMapping firstFrame
  have roots : written.tree.roots = tree.roots := by simpa only [written,GeneralBorrowProtectedMutableRelease.write,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.roots firstFrame
  let nextDepth := GeneralBorrowFreshReadFrame.depth_on tree written.tree nodes depth
  have nextChildren : GeneralBorrowGraph.ChildNodes written.tree := by rw [writtenFrame];exact children
  have nextCovered : GeneralBorrowGraph.RootsCover written.tree := by rw [writtenFrame];exact covered
  have childPresent : written.tree.nodeAt child = some node := by change written.tree.nodes.get child = some node;rw [nodes];exact present
  have rootPresent : written.tree.nodeAt root = some s.node := by change written.tree.nodes.get root = some s.node;rw [nodes];exact s.star.present
  have lookupAfter : written.tree.indexOfTag tag = some child := by change written.tree.tagMapping.get tag = some child;rw [mapping];exact lookup
  have nextFits : written.tree.nodes.data.size ≤ 4294967296 := by rw [nodes];exact fits
  have activeAfter := GeneralBorrowFreshActiveWithinAccess.normal tree tag (Size.ofBytes offset) (Size.ofBytes len) .Write protections .VisitChildrenOfAccessed
    child offset (offset+len) s.well request (Nat.le_refl _) (Nat.le_refl _) active
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
  have scan := GeneralBorrowReleaseProperty.preserves written.tree protections tag child root .Write offset (offset+len) positive
    nextFits nextDepth nextChildren node childPresent unexposed (roots.trans s.roots) nextCovered lookupAfter
    (GeneralBorrowFreshActiveWithin.active_on written.tree child .Write offset (offset+len) facts.2.2.1 activeAfter)
    (LocationInvariant cache root) writtenInvariant.2.1 (by
      intro location range kind good owner kindRead
      obtain ⟨⟨forest⟩,compatible⟩ := owner
      have actual := GeneralBorrowRangePreserves.owned_for_access _ child.toNat kind .Write kindRead compatible
      rw [GeneralBorrowRangePreserves.single_root_location written.tree location protections child root kind .SkipChildrenOfAccessed range forest actual
        nextDepth nextChildren node childPresent (roots.trans s.roots) nextCovered]
      have result := GeneralBorrowRootOnlyProtectedChildCache.normal written.tree location root child s.node node rootPresent s.star.parentless childPresent parent
        kind .SkipChildrenOfAccessed protections writtenInvariant.1 forest actual good.1
      exact ⟨result.1,result.2.trans good.2⟩)
    (by intro position valid positive lower upper;exact facts.2.1 position valid)
  have releaseFrame : released.tree = {written.tree with locations := released.tree.locations} := scan.2.1
  have finalNodes : released.tree.nodes = written.tree.nodes := by simpa only using congrArg BorrowTree.nodes releaseFrame
  refine ⟨?_,scan.2.2,?_⟩
  · intro index value found flag
    rw [finalNodes] at found
    exact writtenInvariant.1 index value found flag
  · rw [finalNodes]
    exact writtenInvariant.2.2

end DuplicatePrefix.GeneralBorrowRootOnlyProtectedRelease
