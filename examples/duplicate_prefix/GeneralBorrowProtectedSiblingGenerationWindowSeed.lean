import duplicate_prefix.GeneralBorrowProtectedReadableFnEntry
import duplicate_prefix.GeneralBorrowFullSharedSeed
import duplicate_prefix.GeneralBorrowGcAllocator
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowSeed
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open DuplicatePrefix.GeneralBorrowProtectedReadRelease (Profile)
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def allocation : AllocId := ⟨1,by decide⟩
def tag2 : BorTag := ⟨2,by decide⟩
def tag3 : BorTag := ⟨3,by decide⟩
def tag4 : BorTag := ⟨4,by decide⟩
def global : GlobalState := {nextPointerTag := tag2,rootPointerTags := #[(allocation,BorTag.one)]}
def initial (capacity : UInt64) : BorrowTree := BorrowTree.new BorTag.one (Size.ofBytes capacity)

theorem root_allocation : GlobalState.new.rootPointerTag allocation = .ok (global,BorTag.one) := rfl

def input (capacity : UInt64) (nonzero : capacity ≠ 0) : GeneralBorrowFreshMetadataChildMutable.Input :=
  let shared := GeneralBorrowFullSharedSeed.input capacity nonzero BorTag.one tag2 (by decide)
  {tree := shared.tree,depth := shared.depth,children := shared.children,covered := shared.covered,
    parentTag := shared.parentTag,newTag := shared.newTag,parent := shared.parent,parentNode := shared.parentNode,
    parentTagPresent := shared.parentTagPresent,parentPresent := shared.parentPresent,fresh := shared.fresh,
    noFree := shared.noFree,aligned := shared.aligned,fits := shared.fits,offset := shared.offset,len := shared.len,
    nonzero := shared.nonzero,well := shared.well,bounds := shared.bounds}

theorem profile (capacity : UInt64) (nonzero : capacity ≠ 0) : Every (Profile (initial capacity) global.protectedTags) (initial capacity).locations := by
  intro position valid
  have validOne : position < 1 := by
    change position < (GeneralBorrowFullSharedSeed.tree capacity nonzero BorTag.one).locations.entries.size at valid
    rw [GeneralBorrowFullSharedSeed.tree_eq] at valid
    exact valid
  have zero : position = 0 := by omega
  subst position
  have locationEq : (initial capacity).locations.entries[0].data = GeneralBorrowFullSharedSeed.location := by
    change (GeneralBorrowFullSharedSeed.tree capacity nonzero BorTag.one).locations.entries[0].data = _
    simp only [GeneralBorrowFullSharedSeed.tree_eq, RangeMapNonempty.homogeneous, Array.getElem_singleton]
  rw [locationEq]
  change Nonempty (GeneralBorrowForest.Forest (source_normal_projection
      (GeneralBorrowFullSharedSeed.tree capacity nonzero BorTag.one) GeneralBorrowFullSharedSeed.location {}).topology) ∧
    GeneralBorrowProtectedReadInvariant.Data (source_normal_projection
      (GeneralBorrowFullSharedSeed.tree capacity nonzero BorTag.one) GeneralBorrowFullSharedSeed.location {})
  rw [GeneralBorrowFullSharedSeed.projection]
  refine ⟨⟨GeneralBorrowFullSharedSeed.normalForest⟩,?_⟩
  intro index bounded
  have zero : index = 0 := by change index < 1 at bounded;omega
  subst index
  exact ⟨GeneralBorrowWildcardLeaf.unique,rfl,by simp [GeneralBorrowProtectedReadInvariant.Readable,GeneralBorrowWildcardLeaf.unique,GeneralBorrowFullSharedSeed.normal,LocationState.possible]⟩

end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationWindowSeed
