import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyCallbackFrame
import duplicate_prefix.GeneralBorrowPositiveWildcardVacantClean
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyScalarClean
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowExposedUniqueRootFamilySeed GeneralBorrowExposedUniqueRootFamilyAppend
open GeneralBorrowExposedUniqueRootFamilyRelease GeneralBorrowProjection
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
theorem activate (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree) (roots : List UniIndex)
    (family : Family capacity global tree location roots) (allocation : AllocId)
    (fresh : global.nextPointerTag.value<18446744073709551615) (room : tree.nodes.size+1<65536)
    (query : UniIndex) (vacant : (after tree global capacity).nodes.get query=none)
    (clean : (locationAfter tree location).perms.get query=none) :
    (writeLocation capacity global tree location allocation fresh).perms.get query=none := by
  obtain ⟨allocatedTag,readDone,builtExact,structural,locations,rootEq,present,stored,cache,old⟩ :=
    GeneralBorrowExposedUniqueRootFamilyAppend.append capacity global tree location roots family allocation fresh room
  cases roots with
  | nil => exact False.elim (family.nonempty rfl)
  | cons head extras =>
    let built := after tree global capacity
    let node := WildcardHitZeroConstructor.rootNode global.nextPointerTag (.ReservedFrz false) .None
    let protections := (registered global fresh allocation).1.protectedTags
    obtain ⟨headNode,headPresent,headParent,headLeaf,headExposed,headStored,headCache,headBelow⟩ := old head (by simp)
    have rootsAfter : built.roots=(head::(extras++[index tree])).toArray := by
      rw [rootEq,family.rootsEq]
      simpa only [List.cons_append] using List.push_toArray (head::extras) (index tree)
    have headBound : headNode.tag.value≤node.tag.value := by
      apply UInt64.le_iff_toNat_le.mpr
      have below := UInt64.lt_iff_toNat_lt.mp headBelow
      exact Nat.le_of_lt below
    have extra : ∀ root∈extras,∃ leaf,built.nodeAt root=some leaf ∧ leaf.children=#[] ∧ leaf.isExposed=true ∧
        (locationAfter tree location).perms.get root=some GeneralBorrowWildcardLeaf.unique ∧
        (locationAfter tree location).exposedCache.nodes.get root=some (⟨1,1⟩:ExposedCacheNode) ∧ leaf.tag.value≤node.tag.value := by
      intro root member
      obtain ⟨leaf,found,parentless,children,exposed,unique,cache,below⟩ := old root (by simp [member])
      exact ⟨leaf,found,children,exposed,unique,cache,UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp below))⟩
    have fits : built.nodes.data.size≤4294967296 := structural.fits
    have localAccess := GeneralBorrowExposedUniqueRootFamilyCallbackFrame.activate built (locationAfter tree location) protections head (index tree) headNode node extras ⟨0,capacity⟩
      rootsAfter headPresent headLeaf headExposed headStored headCache headBound present rfl rfl rfl stored fits extra
    change (source_access_location (source_tree_access_at built (locationAfter tree location) (some (index tree)) .Write protections .VisitChildrenOfAccessed ⟨0,capacity⟩)).perms.get query=none
    rw [localAccess.1]
    obtain ⟨depth⟩ := structural.depth
    exact GeneralBorrowFreshActiveOnClean.normal_vacant built (locationAfter tree location) protections (index tree) query .Write
      .VisitChildrenOfAccessed depth structural.children node present vacant clean

theorem release (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree) (roots : List UniIndex)
    (family : Family capacity global tree location roots) (allocation : AllocId)
    (fresh : global.nextPointerTag.value<18446744073709551615) (room : tree.nodes.size+1<65536)
    (query : UniIndex) (vacant : (after tree global capacity).nodes.get query=none)
    (clean : (writeLocation capacity global tree location allocation fresh).perms.get query=none) :
    (releaseLocation capacity global tree location allocation fresh).perms.get query=none := by
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
    have callback := GeneralBorrowExposedUniqueRootFamilyCallbackFrame.skip current middle protections head (index tree) headNode node extras ⟨0,capacity⟩
      rootsCurrent headFound headLeaf headExposed (activated.2.2.2.2 head (by simp))
      (by rw [cacheEq];exact headCache) (UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt (UInt64.lt_iff_toNat_lt.mp headBelow)))
      newFound rfl rfl rfl activated.2.2.1 fits extra
    change (source_access_location (source_tree_access_at current middle (some (index tree)) .Write protections .SkipChildrenOfAccessed ⟨0,capacity⟩)).perms.get query=none
    rw [callback.1]
    obtain ⟨depth⟩ := structural.depth
    have currentDepth : GeneralBorrowExposure.ParentDepth current.nodes := by rw [currentEq];exact depth
    have currentChildren : GeneralBorrowGraph.ChildNodes current := by rw [currentEq];exact structural.children
    have currentVacant : current.nodes.get query=none := by rw [currentEq];exact vacant
    exact GeneralBorrowFreshActiveOnClean.normal_vacant current middle protections (index tree) query .Write
      .SkipChildrenOfAccessed currentDepth currentChildren node newFound currentVacant clean
end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyScalarClean
