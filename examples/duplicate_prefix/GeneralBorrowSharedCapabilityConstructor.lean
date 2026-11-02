import duplicate_prefix.GeneralBorrowSharedCapabilityShape
import duplicate_prefix.GeneralBorrowSharedConstructorRuntime
namespace DuplicatePrefix.GeneralBorrowSharedCapabilityConstructor
open Miri Miri.ABI Miri.DataStructures Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSharedCapabilityRange GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

namespace Append
open GeneralBorrowFreshMetadataChildShared
/-- Real append plus ancestor SIFA weakening preserves parent Both and creates child Read. -/
theorem capabilities (input : Input) (protections : ProtectedTags)
    (unprotected : protections.contains input.newTag = false)
    (before : OwnedOn (Parent input.tree protections input.parent)
      input.offset (input.offset+input.len) input.tree.locations) :
    OwnedOn (Both (result input) protections input.parent (index input))
      input.offset (input.offset+input.len) (result input).locations := by
  have installed := append_ranged_owned input.tree (index input) input.parent input.parentNode input.newTag
    (at_end input) input.parentPresent protections unprotected (Size.ofBytes input.offset) (Size.ofBytes input.len)
    input.well input.bounds before
  have staged : OwnedOn (Both (stage input) protections input.parent (index input))
      input.offset (input.offset+input.len) (stage input).locations := by
    intro position valid positive start stop
    have row := installed position valid positive start stop
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged] at *
    rw [GeneralBorrowSharedCapabilityRange.context] at row ⊢
    exact row
  exact GeneralBorrowSharedCapabilityShape.shape_preserves (stage input) (result input) (shape input)
    protections input.parent (index input) input.offset (input.offset+input.len) staged
end Append

namespace Reuse
open GeneralBorrowFreshMetadataChildSharedReuse
/-- Vacant-slot reuse plus actual ancestor SIFA weakening yields the same capabilities. -/
theorem capabilities (input : Input) (protections : ProtectedTags)
    (unprotected : protections.contains input.newTag = false)
    (fits : input.tree.nodes.data.size ≤ 4294967296)
    (before : OwnedOn (Parent input.tree protections input.parent)
      input.offset (input.offset+input.len) input.tree.locations) :
    OwnedOn (Both (result input) protections input.parent input.index)
      input.offset (input.offset+input.len) (result input).locations := by
  have installed := reuse_ranged_owned input.tree input.index input.parent input.parentNode input.newTag
    input.valid input.vacant fits input.parentPresent protections unprotected (Size.ofBytes input.offset) (Size.ofBytes input.len)
    input.well input.bounds before
  have staged : OwnedOn (Both (stage input) protections input.parent input.index)
      input.offset (input.offset+input.len) (stage input).locations := by
    intro position valid positive start stop
    have row := installed position valid positive start stop
    dsimp only [stage,GeneralBorrowFreshMetadataChildAttach.staged] at *
    rw [GeneralBorrowSharedCapabilityRange.context] at row ⊢
    exact row
  exact GeneralBorrowSharedCapabilityShape.shape_preserves (stage input) (result input) (shape input)
    protections input.parent input.index input.offset (input.offset+input.len) staged
end Reuse

/-- The actual concrete shared constructor completes, retains complete runtime
facts, and yields both source-specific capabilities on its requested window.
Allocator choice is derived from the raw runtime; arbitrary coherent pools are allowed. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (unprotected : global.protectedTags.contains newTag = false)
    (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (before : OwnedOn (fun location => Nonempty (DuplicatePrefixBorrowAuthorization.Normal tree location global.protectedTags parent))
      offset (offset+len) tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
    ∃ child, actual.tree.indexOfTag newTag = some child ∧
      OwnedOn (Both actual.tree global.protectedTags parent child) offset (offset+len) actual.tree.locations := by
  have initial : OwnedOn (Parent tree global.protectedTags parent) offset (offset+len) tree.locations := by
    intro position valid positive start stop
    exact ⟨runtime.formed.toState.forest _ _,before position valid positive start stop⟩
  have output := GeneralBorrowSharedConstructorRuntime.construct tree global runtime parentTag newTag parent parentNode
    tagged present fresh room tagBound false unprotected offset len nonzero bounds
  refine ⟨output.1,output.2.1,output.2.2.1,output.2.2.2,?_⟩
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  have slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree accounting fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,accounting,fits,false,offset,len,nonzero,runtime.formed.well,bounds⟩
    exact ⟨GeneralBorrowFreshMetadataChildShared.index input,
      (GeneralBorrowFreshMetadataChildShared.append input).freshLookup,Append.capabilities input global.protectedTags unprotected initial⟩
  | reuse index available valid vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        index,available,valid,vacant,slack,false,offset,len,nonzero,runtime.formed.well,bounds⟩
    have fits : tree.nodes.data.size ≤ 4294967296 := by change tree.nodes.data.size+1 ≤ _ at room;omega
    exact ⟨index,(GeneralBorrowFreshMetadataChildSharedReuse.reuse input).freshLookup,
      Reuse.capabilities input global.protectedTags unprotected fits initial⟩

end DuplicatePrefix.GeneralBorrowSharedCapabilityConstructor
