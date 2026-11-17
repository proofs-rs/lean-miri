import duplicate_prefix.GeneralBorrowProtectedCapabilityShape
import duplicate_prefix.GeneralBorrowProtectedConstructorRuntime
namespace DuplicatePrefix.GeneralBorrowProtectedCapabilityConstructor
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProtectedCapabilityRange GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

namespace Append
open GeneralBorrowFreshMetadataChildMutable
/-- Real append plus ancestor SIFA weakening creates the protected child Both Normal. -/
theorem capabilities (input : Input) (protections : ProtectedTags)
    (heldTag : protections.contains input.newTag = true)
    (before : OwnedOn (Parent input.tree protections input.parent)
      input.offset (input.offset+input.len) input.tree.locations) :
    OwnedOn (Child (result input) protections input.parent (index input))
      input.offset (input.offset+input.len) (result input).locations := by
  have installed := append_ranged_owned input.tree (index input) input.parent input.parentNode input.newTag
    (at_end input) input.parentPresent protections heldTag (Size.ofBytes input.offset) (Size.ofBytes input.len)
    input.well input.bounds before
  have staged : OwnedOn (Child (stage input) protections input.parent (index input))
      input.offset (input.offset+input.len) (stage input).locations := by
    intro position valid positive start stop
    have row := installed position valid positive start stop
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged] at *
    rw [GeneralBorrowProtectedCapabilityRange.context] at row ⊢
    exact row
  exact GeneralBorrowProtectedCapabilityShape.shape_preserves (stage input) (result input) (shape input)
    protections input.parent (index input) input.offset (input.offset+input.len) staged
end Append

namespace Reuse
open GeneralBorrowFreshMetadataChildMutableReuse
/-- Vacant-slot reuse plus actual ancestor SIFA weakening yields child Both Normal. -/
theorem capabilities (input : Input) (protections : ProtectedTags)
    (heldTag : protections.contains input.newTag = true)
    (fits : input.tree.nodes.data.size ≤ 4294967296)
    (before : OwnedOn (Parent input.tree protections input.parent)
      input.offset (input.offset+input.len) input.tree.locations) :
    OwnedOn (Child (result input) protections input.parent input.index)
      input.offset (input.offset+input.len) (result input).locations := by
  have installed := reuse_ranged_owned input.tree input.index input.parent input.parentNode input.newTag
    input.valid input.vacant fits input.parentPresent protections heldTag (Size.ofBytes input.offset) (Size.ofBytes input.len)
    input.well input.bounds before
  have staged : OwnedOn (Child (stage input) protections input.parent input.index)
      input.offset (input.offset+input.len) (stage input).locations := by
    intro position valid positive start stop
    have row := installed position valid positive start stop
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged] at *
    rw [GeneralBorrowProtectedCapabilityRange.context] at row ⊢
    exact row
  exact GeneralBorrowProtectedCapabilityShape.shape_preserves (stage input) (result input) (shape input)
    protections input.parent input.index input.offset (input.offset+input.len) staged
end Reuse

/-- The actual concrete mutable Default constructor completes, retains complete runtime
facts, and yields the fresh protected child Both Normal on its requested window.
Allocator choice is derived from the raw runtime; arbitrary coherent pools are allowed. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (heldTag : global.protectedTags.contains newTag = true)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (before : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags parent))
      offset (offset+len) tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
    ∃ child, actual.tree.indexOfTag newTag = some child ∧
      OwnedOn (Child actual.tree global.protectedTags parent child) offset (offset+len) actual.tree.locations := by
  have initial : OwnedOn (Parent tree global.protectedTags parent) offset (offset+len) tree.locations := by
    intro position valid positive start stop
    exact ⟨runtime.formed.toState.forest _ _,before position valid positive start stop⟩
  have output := GeneralBorrowProtectedConstructorRuntime.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound heldTag offset len nonzero bounds
  refine ⟨output.1,output.2.1,output.2.2.1,output.2.2.2,?_⟩
  let rank := GeneralBorrowStructuralHistoryMutable.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryMutable.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildMutable.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,offset,len,nonzero,runtime.formed.well,bounds⟩
    exact ⟨GeneralBorrowFreshMetadataChildMutable.index input,
      (GeneralBorrowFreshMetadataChildMutable.append input).freshLookup,Append.capabilities input global.protectedTags heldTag initial⟩
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildMutableReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,valid,vacant,slack,offset,len,nonzero,runtime.formed.well,bounds⟩
    have fits : tree.nodes.data.size ≤ 4294967296 := by change tree.nodes.data.size+1 ≤ _ at room;omega
    exact ⟨index,(GeneralBorrowFreshMetadataChildMutableReuse.reuse input).freshLookup,
      Reuse.capabilities input global.protectedTags heldTag fits initial⟩

end DuplicatePrefix.GeneralBorrowProtectedCapabilityConstructor
