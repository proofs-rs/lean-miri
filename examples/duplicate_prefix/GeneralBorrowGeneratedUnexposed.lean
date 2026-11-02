import duplicate_prefix.GeneralBorrowSharedUnexposed
import duplicate_prefix.GeneralBorrowGeneratedStarShape
namespace DuplicatePrefix.GeneralBorrowGeneratedUnexposed
open Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowFreshMetadataChildShared DuplicatePrefix.GeneralBorrowFullSharedRead
open DuplicatePrefix.GeneralBorrowFullSharedStep DuplicatePrefix.GeneralBorrowGeneratedStarShape
open DuplicatePrefix.GeneralBorrowSharedUnexposed DuplicatePrefix.RangeMapNonempty
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

attribute [local irreducible] GeneralBorrowFreshMetadataChildShared.result GeneralBorrowFreshMetadataChildShared.stage

/-- Every actual successor retains all-unexposed metadata and its original cache. -/
theorem successor (input : Input) (location : LocationTree) (good : State input location)
    (star : Star input.tree input.parent input.parentNode) (initial : Unexposed input.tree)
    (next : Input) (tree : next.tree = (child input {}).tree) (parent : next.parent = input.parent)
    (length : next.len = input.len) :
    ∃ postLocation, State next postLocation ∧ Star next.tree next.parent next.parentNode ∧
      Unexposed next.tree ∧ postLocation.exposedCache = location.exposedCache := by
  obtain ⟨postLocation,nextGood,nextStar⟩ := GeneralBorrowGeneratedStarShape.successor input location good star next tree parent length
  obtain ⟨forest⟩ := good.forest
  let prepared := afterReadInput input location {} good.offset
  have readFacts := read_closed input location good.offset good.locations good.roots good.parentless forest good.profile
  have actualChild : child input {} = prepared.tree.newChild (Size.ofBytes prepared.offset)
      (.concrete prepared.parentTag) prepared.newTag (DedupRangeMap.new (Size.ofBytes prepared.len)
        GeneralBorrowFreshAnchor.sharedState) .Frozen prepared.isProtected := by
    unfold child
    rw [readFacts.2.1]
    simp only [prepared,afterReadInput]
  have childTree : (child input {}).tree = result prepared := by rw [actualChild];unfold result;rfl
  obtain ⟨actualLocation,locations,profile,cache⟩ := GeneralBorrowFullSharedAppend.append prepared
    (readLocation input location {}) good.offset rfl good.parentless readFacts.2.2.1
  have sameLocations : homogeneous input.len postLocation = homogeneous input.len actualLocation := by
    calc
      homogeneous input.len postLocation = homogeneous next.len postLocation := by rw [length]
      _ = next.tree.locations := nextGood.locations.symm
      _ = homogeneous input.len actualLocation := by rw [tree,childTree];exact locations
  have same : postLocation = actualLocation := by
    have projected := congrArg (fun m : DedupRangeMap LocationTree => (m.entries[0]?).map (fun seg => seg.data)) sameLocations
    simpa only [homogeneous,Array.getElem?_singleton,ite_true,Option.map_some,Option.some.injEq] using projected
  refine ⟨postLocation,nextGood,nextStar,?_,?_⟩
  · rw [tree,childTree]
    exact read_append input location {} good.offset initial
  · rw [same,cache]
    exact read_cache input location {} initial

/-- Induction over real completed operations preserves node flags and the
actual cache; allocation-to-history theorems construct the Run internally. -/
theorem run {input final : Input} {tags : List BorTag}
    (history : GeneralBorrowFullSharedRepeat.Run input tags final)
    (location : LocationTree) (good : State input location)
    (star : Star input.tree input.parent input.parentNode) (initial : Unexposed input.tree) :
    ∃ finalLocation, State final finalLocation ∧ Star final.tree final.parent final.parentNode ∧
      Unexposed final.tree ∧ finalLocation.exposedCache = location.exposedCache := by
  induction history generalizing location with
  | nil => exact ⟨location,good,star,initial,rfl⟩
  | cons readDone childDone tree parent newTag length tail ih =>
    obtain ⟨nextLocation,nextGood,nextStar,nextInitial,cache⟩ := successor _ location good star initial _ tree parent length
    obtain ⟨finalLocation,finalGood,finalStar,finalInitial,finalCache⟩ := ih nextLocation nextGood nextStar nextInitial
    exact ⟨finalLocation,finalGood,finalStar,finalInitial,finalCache.trans cache⟩

/-- The actual allocator creates only an unexposed root. -/
theorem seed (capacity : UInt64) (nonzero : capacity ≠ 0) (rootTag childTag : BorTag)
    (different : rootTag ≠ childTag) :
    Unexposed (GeneralBorrowFullSharedSeed.input capacity nonzero rootTag childTag different).tree := by
  intro query node present
  have valid := GeneralBorrowNodeUpdate.lookup_valid _ query node present
  change query.toNat < (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).nodes.data.size at valid
  rw [GeneralBorrowFullSharedSeed.tree_eq] at valid
  change query.toNat < 1 at valid
  have same : query = GeneralBorrowFullSharedSeed.root := GeneralBorrowNodeUpdate.index_injective _ _ (by change query.toNat = 0;omega)
  subst query
  change (GeneralBorrowFullSharedSeed.tree capacity nonzero rootTag).nodeAt _ = some node at present
  rw [GeneralBorrowFullSharedSeed.tree_eq] at present
  change some (GeneralBorrowFullSharedSeed.node rootTag) = some node at present
  cases present
  rfl
end DuplicatePrefix.GeneralBorrowGeneratedUnexposed
