import duplicate_prefix.GeneralBorrowRootExposureSeed
import duplicate_prefix.GeneralBorrowProtectedLifetimeSeed
import duplicate_prefix.GeneralBorrowExposureAllocation
import duplicate_prefix.GeneralBorrowStructuralHistoryFrames
import duplicate_prefix.GeneralBorrowStructuralHistorySeed
namespace DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilySeed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open RangeMapNonempty GeneralBorrowRootExposureSeed
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- SourceModel formation invariant for parentless exposed Unique leaves.
Every assigned tag lies below the real global tag allocator's high-water mark. -/
structure Family (capacity : UInt64) (global : GlobalState) (tree : BorrowTree) (location : LocationTree) (roots : List UniIndex) : Prop where
  structural : GeneralBorrowStructuralHistoryState.State tree
  nonzero : capacity≠0
  locations : tree.locations=homogeneous capacity location
  rootsEq : tree.roots=roots.toArray
  nonempty : roots≠[]
  noFree : tree.tagMapping.deassigned.back?=none
  aligned : tree.tagMapping.mapping.size=tree.nodes.data.size
  emptyProtections : global.protectedTags={}
  coherent : GeneralBorrowExposureCardinality.LocationCoherent tree location global.protectedTags
  leaves : ∀ root∈roots,∃ node,tree.nodeAt root=some node ∧ node.parent=none ∧ node.children=#[] ∧ node.isExposed=true ∧
    location.perms.get root=some GeneralBorrowWildcardLeaf.unique ∧ location.exposedCache.nodes.get root=some (⟨1,1⟩:ExposedCacheNode)
  allNodes : ∀ index node,tree.nodeAt index=some node → index∈roots
  highWater : ∀ row∈tree.tagMapping.mapping.toList,row.1.value<global.nextPointerTag.value
  cacheBound : location.exposedCache.nodes.size≤tree.nodes.size
  size : tree.nodes.size=roots.length

/-- Actual global root-tag allocation, BorrowTree.new and first root exposure
form the initial family for every positive allocation size. No exposure,
Unique, cache or allocator certificate is a premise. -/
theorem seed (capacity : UInt64) (nonzero : capacity≠0) :
    GlobalState.new.rootPointerTag GeneralBorrowProtectedLifetimeSeed.allocation=
      .ok (GeneralBorrowProtectedLifetimeSeed.global,BorTag.one) ∧
    let initial := BorrowTree.new BorTag.one (Size.ofBytes capacity)
    let exposed := initial.exposeTag GeneralBorrowProtectedLifetimeSeed.global.protectedTags BorTag.one
    exposed.outcome=.ok () ∧ Family capacity GeneralBorrowProtectedLifetimeSeed.global exposed.tree exposedLocation [root] := by
  refine ⟨GeneralBorrowProtectedLifetimeSeed.root_allocation,?_⟩
  dsimp only
  rw [GeneralBorrowRootExposureSeed.expose capacity nonzero BorTag.one]
  refine ⟨rfl,?_⟩
  let initial := BorrowTree.new BorTag.one (Size.ofBytes capacity)
  have structural := GeneralBorrowStructuralHistoryFrames.expose initial (GeneralBorrowStructuralHistorySeed.initial BorTag.one (Size.ofBytes capacity))
    BorTag.one GeneralBorrowProtectedLifetimeSeed.global.protectedTags
  have original := GeneralBorrowFullSharedSeed.tree_eq capacity nonzero BorTag.one
  have originalEq : initial=GeneralBorrowFullSharedSeed.tree capacity nonzero BorTag.one := rfl
  have rootPresent : initial.nodeAt root=some (rootNode BorTag.one false) := by rw [originalEq,original];rfl
  have tagPresent : initial.indexOfTag BorTag.one=some root := by rw [originalEq,original];rfl
  have depth := GeneralBorrowFullSharedSeed.depth capacity nonzero BorTag.one
  have caches := GeneralBorrowPartitionExposeCardinality.expose initial GeneralBorrowProtectedLifetimeSeed.global.protectedTags root (rootNode BorTag.one false)
    rootPresent tagPresent depth (GeneralBorrowExposureAllocation.coherent capacity BorTag.one _)
  have exposedEq : initial.exposeTag GeneralBorrowProtectedLifetimeSeed.global.protectedTags BorTag.one=
      ⟨exposedTree capacity BorTag.one,.ok ()⟩ := GeneralBorrowRootExposureSeed.expose capacity nonzero BorTag.one _
  simp only [rootNode] at caches
  rw [exposedEq] at structural caches
  refine ⟨structural.1,nonzero,rfl,rfl,(by simp),rfl,rfl,rfl,?_,?_,?_,?_,(by change (1:Nat)≤1;omega),rfl⟩
  · exact caches.2 0 (by change 0<1;decide)
  · intro query member
    have same : query=root := by simpa using member
    subst query
    exact ⟨rootNode BorTag.one true,rfl,rfl,rfl,rfl,rfl,rfl⟩
  · intro query node present
    have bound := GeneralBorrowNodeUpdate.lookup_valid (exposedTree capacity BorTag.one).nodes query node present
    have same : query=root := GeneralBorrowNodeUpdate.index_injective _ _ (by change query.toNat=0;change query.toNat<1 at bound;omega)
    simp [same]
  · intro row member
    have same : row=(BorTag.one,root) := by simpa only [exposedTree,Array.toList_push,Array.toList_empty,List.nil_append,List.mem_cons,List.mem_nil_iff,or_false] using member
    subst row
    decide
end DuplicatePrefix.GeneralBorrowExposedUniqueRootFamilySeed
