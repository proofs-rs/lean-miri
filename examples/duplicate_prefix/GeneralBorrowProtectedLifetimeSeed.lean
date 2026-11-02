import duplicate_prefix.GeneralBorrowProtectedReadableFnEntry
import duplicate_prefix.GeneralBorrowFullSharedSeed
import duplicate_prefix.GeneralBorrowGcAllocator
namespace DuplicatePrefix.GeneralBorrowProtectedLifetimeSeed
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
def initial : BorrowTree := BorrowTree.new BorTag.one (Size.ofBytes 1)

theorem root_allocation : GlobalState.new.rootPointerTag allocation = .ok (global,BorTag.one) := rfl

def input : GeneralBorrowFreshMetadataChildMutable.Input :=
  let shared := GeneralBorrowFullSharedSeed.input 1 (by decide) BorTag.one tag2 (by decide)
  {tree := shared.tree,depth := shared.depth,children := shared.children,covered := shared.covered,
    parentTag := shared.parentTag,newTag := shared.newTag,parent := shared.parent,parentNode := shared.parentNode,
    parentTagPresent := shared.parentTagPresent,parentPresent := shared.parentPresent,fresh := shared.fresh,
    noFree := shared.noFree,aligned := shared.aligned,fits := shared.fits,offset := shared.offset,len := shared.len,
    nonzero := shared.nonzero,well := shared.well,bounds := shared.bounds}

theorem profile : Every (Profile initial global.protectedTags) initial.locations := by
  intro position valid
  have zero : position = 0 := by change position < 1 at valid;omega
  subst position
  change Nonempty (GeneralBorrowForest.Forest (source_normal_projection
      (GeneralBorrowFullSharedSeed.tree 1 (by decide) BorTag.one) GeneralBorrowFullSharedSeed.location {}).topology) ∧
    GeneralBorrowProtectedReadInvariant.Data (source_normal_projection
      (GeneralBorrowFullSharedSeed.tree 1 (by decide) BorTag.one) GeneralBorrowFullSharedSeed.location {})
  rw [GeneralBorrowFullSharedSeed.projection]
  refine ⟨⟨GeneralBorrowFullSharedSeed.normalForest⟩,?_⟩
  intro index bounded
  have zero : index = 0 := by change index < 1 at bounded;omega
  subst index
  exact ⟨GeneralBorrowWildcardLeaf.unique,rfl,by simp [GeneralBorrowProtectedReadInvariant.Readable,GeneralBorrowWildcardLeaf.unique,GeneralBorrowFullSharedSeed.normal,LocationState.possible]⟩

theorem clean (query : UniIndex) (outside : 1 ≤ query.toNat) :
    Every (fun location : LocationTree => location.perms.get query = none) initial.locations := by
  intro position valid
  have zero : position = 0 := by change position < 1 at valid;omega
  subst position
  change (⟨#[some GeneralBorrowWildcardLeaf.unique]⟩ : UniValMap LocationState).get query = none
  unfold UniValMap.get
  rw [Array.getElem?_eq_none (by simpa only [Array.size_singleton] using outside)]

theorem nodeTags : ∀ index node,initial.nodeAt index = some node → initial.indexOfTag node.tag = some index :=
  (GeneralBorrowGcAllocator.initial BorTag.one (Size.ofBytes 1)).nodeTags
end DuplicatePrefix.GeneralBorrowProtectedLifetimeSeed
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowProtectedLifetimeSeed.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved protected lifetime seed dependency {dependency}"
