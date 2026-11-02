import duplicate_prefix.GeneralBorrowForestGeneratedHiddenConcrete
import duplicate_prefix.GeneralBorrowForestGeneratedHiddenWildcard
import duplicate_prefix.GeneralBorrowNormalRangeExposureCache
import duplicate_prefix.GeneralBorrowProtectorReleaseCache
namespace DuplicatePrefix.GeneralBorrowForestGeneratedHiddenOperations
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowForestGeneratedTagHistoryData GeneralBorrowForestGeneratedSifaHistory GeneralBorrowForestGeneratedHiddenCache GeneralRangeMapState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

theorem seed (tag : BorTag) (size : Size) : Empty (BorrowTree.new tag size) := by
  refine ⟨?_,?_⟩
  · intro index node found
    have valid := GeneralBorrowNodeUpdate.lookup_valid _ index node found
    change index.toNat<1 at valid
    have same : index=(⟨0⟩:UniIndex) := GeneralBorrowNodeUpdate.index_injective _ _ (by change index.toNat=0;omega)
    subst index
    change some _=some node at found
    cases found
    rfl
  · unfold BorrowTree.new
    simp only [Id.run,pure,DedupRangeMap.new]
    split
    · intro position valid
      change position<0 at valid
      omega
    · intro position valid query kind
      have same : position=0 := by change position<1 at valid;omega
      subst position
      cases kind <;> rfl

theorem collect (tree : BorrowTree) (formed : GeneralBorrowStructuralHistoryState.State tree) (empty : Empty tree) (live : Array BorTag) :
    Empty (tree.removeUnreachableTags live).tree := by
  have hidden : Hidden (tree.removeUnreachableTags live).tree := by
    intro index node found
    obtain ⟨old,present,fields⟩ := GeneralBorrowGcNodeMetadata.collect tree live index node found
    rw[fields.exposed]
    exact empty.hidden index old present
  obtain ⟨depth⟩ := formed.depth
  obtain ⟨forest⟩ := formed.forest {} {}
  have retained : GeneralBorrowGcExposedRetained.ExposedLive tree live := by
    intro index node present exposed
    rw[empty.hidden index node present] at exposed
    cases exposed
  have good := GeneralBorrowGcForestCachePreservation.collect tree {} {} forest depth formed.children formed.fits formed.rootNodes formed.well live retained (coherent tree {} empty)
  exact zero_of_coherent _ {} hidden good.2

theorem owned_read (id : AllocId) (state : Snapshot) (formed : Formed state) (empty : Empty state.tree)
    (tag : BorTag) (offset len : Size) (mode : ChildrenVisitMode)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤state.tree.locations.size.bytes.toNat)
    (data : GeneralBorrowForestGeneratedReadReleaseData.ReadData state tag offset len) :
    Empty (step id state (.access (.concrete tag) offset len .Read mode)).state.tree := by
  obtain ⟨depth⟩ := formed.generated.structural.depth
  have actual := GeneralBorrowNormalRangeExposureCache.ranged state.tree state.global.protectedTags tag data.anchor data.root offset len .Read mode
    depth formed.generated.structural.children data.node data.present data.roots formed.generated.structural.covered data.tagged
    formed.generated.structural.well (coherent _ _ empty) data.lower data.upper data.owned data.requestLower data.requestUpper bounds
  have hidden : Hidden (state.tree.performNormalAccessRange tag offset len .Read state.global.protectedTags mode).tree := by
    intro index node present
    change (state.tree.performNormalAccessRange tag offset len .Read state.global.protectedTags mode).tree.nodes.get index=some node at present
    rw[actual.2.2.2.2.1] at present
    exact empty.hidden index node present
  exact zero_of_coherent _ state.global.protectedTags hidden actual.2.1

theorem release (id : AllocId) (state : Snapshot) (formed : Formed state) (empty : Empty state.tree)
    (data : GeneralBorrowForestGeneratedReadReleaseData.ReleaseData state) : Empty (step id state .release).state.tree := by
  obtain ⟨depth⟩ := formed.generated.structural.depth
  have active := GeneralBorrowFreshActiveWithin.active_on state.tree data.anchor data.ownerKind data.lower data.upper formed.generated.structural.well data.active
  have actual := GeneralBorrowProtectorReleaseCache.release state.tree state.global.protectedTags data.anchor data.root data.ownerKind data.lower data.upper data.positive
    formed.generated.structural.fits depth formed.generated.structural.children data.node data.present (empty.hidden _ _ data.present)
    data.roots formed.generated.structural.covered data.tagged formed.generated.structural.allocator.nodeTags active data.owned (coherent _ _ empty)
  have hidden : Hidden (state.tree.releaseProtector data.node.tag state.global.protectedTags).tree := by
    intro index node present
    rw[actual.2.1] at present
    exact empty.hidden index node present
  have after := zero_of_coherent _ state.global.protectedTags hidden actual.2.2.1
  have status : (state.tree.releaseProtector data.tag state.global.protectedTags).status=.Released := by simpa only[data.sameTag] using actual.1
  simpa only[step,data.last,status,beq_self_eq_true,↓reduceIte,data.sameTag] using after
end DuplicatePrefix.GeneralBorrowForestGeneratedHiddenOperations
