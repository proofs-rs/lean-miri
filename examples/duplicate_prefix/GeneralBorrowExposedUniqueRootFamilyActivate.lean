import duplicate_prefix.GeneralBorrowExposedUniqueRootFamilyAppend
import duplicate_prefix.GeneralBorrowExposedLeafRootActivation
import duplicate_prefix.GeneralBorrowHomogeneousSourceAccess
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyActivate
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowExposedUniqueRootFamilySeed GeneralBorrowExposedUniqueRootFamilyAppend
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Full positive activation after the real wildcard append, retaining every
older exposed leaf's exact Unique row and every exposure counter. -/
theorem activate (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree) (roots : List UniIndex)
    (family : Family capacity global tree location roots) (allocation : AllocId)
    (fresh : global.nextPointerTag.value<18446744073709551615) (room : tree.nodes.size+1<65536) :
    let built := after tree global capacity
    let protections := (registered global fresh allocation).1.protectedTags
    let nextLocation := source_access_location (source_tree_access_at built (locationAfter tree location) (some (index tree)) .Write protections .VisitChildrenOfAccessed ⟨0,capacity⟩)
    let written := built.performBorrowAccessRange (.concrete global.nextPointerTag) Size.ZERO (Size.ofBytes capacity) .Write protections .VisitChildrenOfAccessed
    written.status=.Completed ∧ written.tree={built with locations:=RangeMapNonempty.homogeneous capacity nextLocation} ∧
      nextLocation.perms.get (index tree)=some GeneralBorrowWildcardLeaf.unique ∧ nextLocation.exposedCache=location.exposedCache ∧
      ∀ root∈roots,nextLocation.perms.get root=some GeneralBorrowWildcardLeaf.unique := by
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
    have localAccess := GeneralBorrowExposedLeafRootActivation.access built (locationAfter tree location) protections head (index tree) headNode node extras ⟨0,capacity⟩
      rootsAfter headPresent headLeaf headExposed headStored headCache headBound present rfl rfl rfl stored fits extra
    have tagged : built.indexOfTag global.nextPointerTag=some (index tree) := by
      have mapped := structural.allocator.nodeTags (index tree) node present
      simpa only [GeneralBorrowGcAllocator.NodeTags,WildcardHitZeroConstructor.rootNode,BorrowTree.indexOfTag,node,built] using mapped
    have ranged := GeneralBorrowHomogeneousSourceAccess.full built (locationAfter tree location) capacity family.nonzero locations
      (.concrete global.nextPointerTag) (some (index tree)) .Write protections .VisitChildrenOfAccessed ⟨tagged,by simp⟩ localAccess.1
    refine ⟨ranged.1,ranged.2,localAccess.2.1,localAccess.2.2.1,?_⟩
    intro root member
    exact (localAccess.2.2.2 root member).trans (old root member).choose_spec.2.2.2.2.1
end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilyActivate
