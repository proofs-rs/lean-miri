import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyActivate
import duplicate_prefix.GeneralBorrowHomogeneousHiddenUniqueRelease
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyRelease
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowExposedUniqueRootFamilySeed GeneralBorrowExposedUniqueRootFamilyAppend
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def writeLocation (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree)
    (allocation : AllocId) (fresh : global.nextPointerTag.value<18446744073709551615) : LocationTree :=
  source_access_location (source_tree_access_at (after tree global capacity) (locationAfter tree location) (some (index tree))
    .Write (registered global fresh allocation).1.protectedTags .VisitChildrenOfAccessed ⟨0,capacity⟩)
def written (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (allocation : AllocId)
    (fresh : global.nextPointerTag.value<18446744073709551615) :=
  (after tree global capacity).performBorrowAccessRange (.concrete global.nextPointerTag) Size.ZERO (Size.ofBytes capacity)
    .Write (registered global fresh allocation).1.protectedTags .VisitChildrenOfAccessed

def releaseLocation (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree)
    (allocation : AllocId) (fresh : global.nextPointerTag.value<18446744073709551615) : LocationTree :=
  source_access_location (source_tree_access_at (written capacity global tree allocation fresh).tree (writeLocation capacity global tree location allocation fresh)
    (some (index tree)) .Write (registered global fresh allocation).1.protectedTags .SkipChildrenOfAccessed ⟨0,capacity⟩)

/-- The actual full-range activated-root release performs its real associated
Write under the Strong protector and retains exact Unique/counters at all roots. -/
theorem release (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree) (roots : List UniIndex)
    (family : Family capacity global tree location roots) (allocation : AllocId)
    (fresh : global.nextPointerTag.value<18446744073709551615) (room : tree.nodes.size+1<65536) :
    let current := written capacity global tree allocation fresh
    let finalLocation := releaseLocation capacity global tree location allocation fresh
    let released := current.tree.releaseProtector global.nextPointerTag (registered global fresh allocation).1.protectedTags
    released=⟨{current.tree with locations:=RangeMapNonempty.homogeneous capacity finalLocation},.Released⟩ ∧
      finalLocation.perms.get (index tree)=some GeneralBorrowWildcardLeaf.unique ∧
      finalLocation.exposedCache=location.exposedCache ∧
      ∀ root∈roots,finalLocation.perms.get root=some GeneralBorrowWildcardLeaf.unique := by
  obtain ⟨allocatedTag,readDone,builtExact,structural,locations,rootEq,present,stored,cache,old⟩ :=
    GeneralBorrowExposedUniqueRootFamilyAppend.append capacity global tree location roots family allocation fresh room
  have activated := GeneralBorrowExposedUniqueRootFamilyActivate.activate capacity global tree location roots family allocation fresh room
  change (written capacity global tree allocation fresh).status=.Completed ∧
    (written capacity global tree allocation fresh).tree={after tree global capacity with locations:=RangeMapNonempty.homogeneous capacity (writeLocation capacity global tree location allocation fresh)} ∧
    (writeLocation capacity global tree location allocation fresh).perms.get (index tree)=some GeneralBorrowWildcardLeaf.unique ∧
    (writeLocation capacity global tree location allocation fresh).exposedCache=location.exposedCache ∧
    (∀ root∈roots,(writeLocation capacity global tree location allocation fresh).perms.get root=some GeneralBorrowWildcardLeaf.unique) at activated
  cases roots with
  | nil => exact False.elim (family.nonempty rfl)
  | cons head extras =>
    let current := (written capacity global tree allocation fresh).tree
    let middle := writeLocation capacity global tree location allocation fresh
    let node := WildcardHitZeroConstructor.rootNode global.nextPointerTag (.ReservedFrz false) .None
    let protections := (registered global fresh allocation).1.protectedTags
    have currentEq : current={after tree global capacity with locations:=RangeMapNonempty.homogeneous capacity middle} := activated.2.1
    have cacheEq : middle.exposedCache=location.exposedCache := activated.2.2.2.1
    obtain ⟨headNode,headPresent,headParent,headLeaf,headExposed,headStored,headCache,headBelow⟩ := old head (by simp)
    have headFound : current.nodeAt head=some headNode := by rw [currentEq];exact headPresent
    have newFound : current.nodeAt (index tree)=some node := by rw [currentEq];exact present
    have rootsCurrent : current.roots=(head::(extras++[index tree])).toArray := by
      rw [currentEq,rootEq,family.rootsEq]
      simpa only [List.cons_append] using List.push_toArray (head::extras) (index tree)
    have extra : ∀ root∈extras,∃ leaf,current.nodeAt root=some leaf ∧ leaf.children=#[] ∧ leaf.isExposed=true ∧
        middle.perms.get root=some GeneralBorrowWildcardLeaf.unique ∧ middle.exposedCache.nodes.get root=some (⟨1,1⟩:ExposedCacheNode) ∧
        leaf.tag.value≤node.tag.value := by
      intro root member
      obtain ⟨leaf,found,parentless,children,exposed,unique,cache,below⟩ := old root (by simp [member])
      exact ⟨leaf,(by rw [currentEq];exact found),children,exposed,activated.2.2.2.2 root (by simp [member]),
        (by rw [cacheEq];exact cache),UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp below))⟩
    have fits : current.nodes.data.size≤4294967296 := by rw [currentEq];exact structural.fits
    have callback := GeneralBorrowExposedLeafRootUniqueSkip.access current middle protections head (index tree) headNode node extras ⟨0,capacity⟩
      rootsCurrent headFound headLeaf headExposed (activated.2.2.2.2 head (by simp))
      (by rw [cacheEq];exact headCache) (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp headBelow)))
      newFound rfl rfl rfl activated.2.2.1 fits extra
    have tagged : current.indexOfTag global.nextPointerTag=some (index tree) := by
      have mapped := structural.allocator.nodeTags (index tree) node present
      rw [currentEq]
      simpa only [BorrowTree.indexOfTag,WildcardHitZeroConstructor.rootNode,node] using mapped
    have exactRelease := GeneralBorrowHomogeneousHiddenUniqueRelease.release current middle capacity protections global.nextPointerTag (index tree) node
      (by rw [currentEq]) tagged newFound rfl activated.2.2.1 callback.1
    refine ⟨exactRelease,callback.2.1,callback.2.2.1.trans activated.2.2.2.1,?_⟩
    intro root member
    exact (callback.2.2.2 root member).trans (activated.2.2.2.2 root member)
end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyRelease
