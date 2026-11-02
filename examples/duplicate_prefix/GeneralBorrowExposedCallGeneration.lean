import duplicate_prefix.GeneralBorrowExposedWriteFresh
namespace DuplicatePrefix.GeneralBorrowExposedCallGeneration
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedStep
open DuplicatePrefix.GeneralBorrowGeneratedStarShape DuplicatePrefix.GeneralBorrowExposedProtocolWrite
open DuplicatePrefix.GeneralBorrowExposedStarFormation DuplicatePrefix.GeneralBorrowExposureHistoryBounds
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

set_option autoImplicit false in
/-- A concrete allocation/generated/exposed/written tree for the physical
caller. All graph, cache, permission and freshness data are constructed. -/
structure Generated (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag)
    (different : rootTag ≠ childTag) (tags : List BorTag) (reserve : Fin 5 → BorTag) where
  final : Input
  exposed : GeneralBorrowExposedStarFormation.Output final
  history : GeneralBorrowFullSharedRepeat.Run
    (GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different) tags final
  completed : (operation final exposed).status = .Completed
  state : GeneralBorrowPartitionState.State (operation final exposed).tree final.parent capacity
  fresh : GeneralBorrowTagMap.Fresh (operation final exposed).tree.tagMapping final.newTag
  reserved : ∀ i,GeneralBorrowTagMap.Fresh (operation final exposed).tree.tagMapping (reserve i)
  exposedFlags : ∀ index node,(operation final exposed).tree.nodeAt index = some node → node.isExposed = true
  postLocation : LocationTree
  locations : (operation final exposed).tree.locations = RangeMapNonempty.homogeneous capacity postLocation
  rootRead : reads postLocation.exposedCache final.parent = 1
  rootWrite : writes postLocation.exposedCache final.parent = 1
  otherCache : ∀ query,query ≠ final.parent → reads postLocation.exposedCache query = 0 ∧ writes postLocation.exposedCache query = 0
  disabled : ∀ index node,(operation final exposed).tree.nodeAt index = some node → index ≠ final.parent →
    ∃ state,postLocation.perms.get index = some state ∧ state.permission = .Disabled

def tree {capacity nonzero rootTag childTag different tags reserve} (g : Generated capacity nonzero rootTag childTag different tags reserve) :=
  (operation g.final g.exposed).tree

/-- Reserved tags are external finite resources, while every initial invariant,
operation completion and final permission/cache/freshness fact is derived. -/
def generate (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag)
    (different : rootTag ≠ childTag) (tags : List BorTag) (distinct : tags.Nodup)
    (rootUnused : rootTag ∉ tags) (childUnused : childTag ∉ tags)
    (reserve : Fin 5 → BorTag) (reserved : ∀ i,reserve i ∉ rootTag::childTag::tags)
    (short : 2+tags.length < 65536) : Generated capacity nonzero rootTag childTag different tags reserve := by
  apply Classical.choice
  let seed := GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different
  have good := GeneralBorrowFullSharedSeed.state capacity nonzero rootTag childTag different
  have singletonFresh : ∀ tag,rootTag ≠ tag → GeneralBorrowTagMap.Fresh seed.tree.tagMapping tag := by
    intro tag different row member
    change row ∈ (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).tagMapping.mapping at member
    rw [GeneralBorrowFullSharedSeed.tree_eq] at member
    have same := Array.mem_singleton.mp member
    subst row;exact different
  have fresh : ∀ tag ∈ tags,GeneralBorrowTagMap.Fresh seed.tree.tagMapping tag := by
    intro tag member;apply singletonFresh tag
    intro same;apply rootUnused;rw [same];exact member
  have spareFresh : ∀ i,GeneralBorrowTagMap.Fresh seed.tree.tagMapping (reserve i) := by
    intro i;apply singletonFresh;intro same;exact reserved i (by simp [same])
  have spareCurrent : ∀ i,seed.newTag ≠ reserve i := by
    intro i same;exact reserved i (by simp [show childTag = reserve i from same])
  have spareFuture : ∀ tag ∈ tags,∀ i,tag ≠ reserve i := by
    intro tag member i same;exact reserved i (by simp [←same,member])
  have initialSize : seed.tree.tagMapping.mapping.size = 1 := by
    change (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).tagMapping.mapping.size = 1
    rw [GeneralBorrowFullSharedSeed.tree_eq];rfl
  obtain ⟨final,ignoredLocation,history,ignoredGood,allocator,size,spares⟩ :=
    GeneralBorrowFullSharedResources.iterate tags seed GeneralBorrowFullSharedSeed.location good
      (GeneralBorrowGcAllocator.initial rootTag (Size.ofBytes capacity)) fresh distinct childUnused
      reserve spareFresh spareCurrent spareFuture (by rw [initialSize];omega)
  obtain ⟨location,finalGood,star,unexposed,cache⟩ := GeneralBorrowGeneratedUnexposed.run history
    GeneralBorrowFullSharedSeed.location good (seed_star capacity nonzero rootTag childTag different)
    (GeneralBorrowGeneratedUnexposed.seed capacity nonzero rootTag childTag different)
  have aligned : final.tree.nodes.size = final.tree.tagMapping.mapping.size := final.aligned.symm
  have room : final.tree.nodes.size+4 ≤ 4294967295 := by rw [aligned,size,initialSize];omega
  have counterRoom : final.parentNode.children.size+1 < 65536 := by
    have bounded := children_bound final.tree final.parent final.parentNode star
    rw [aligned,size,initialSize] at bounded;omega
  let exposed := Classical.choice (form final location finalGood star allocator room unexposed cache counterRoom)
  have wrote := GeneralBorrowExposedProtocolWrite.write final exposed
  let state := Classical.choice wrote.2.1
  have length : final.len = capacity := history.length
  obtain ⟨postLocation,locations,rootRead,rootWrite,other,disabled⟩ := GeneralBorrowExposedWriteDisabled.write final exposed
  have mapping := GeneralBorrowExposedWriteFresh.mapping final exposed
  exact ⟨⟨final,exposed,history,wrote.1,by simpa only [length] using state,
    by rw [mapping];exact final.fresh,by intro i;rw [mapping];exact spares i,wrote.2.2.1,postLocation,
    by rw [length] at locations;exact locations,rootRead,rootWrite,other,disabled⟩⟩
end
end DuplicatePrefix.GeneralBorrowExposedCallGeneration
