import duplicate_prefix.CurrentCallOptionalLenAssociatedRead
import duplicate_prefix.CurrentCallOptionalSharedOldAuthority

namespace DuplicatePrefix.CurrentCallOptionalLenFuture
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership GeneralBorrowExposedNonleafPrimaryPath
open CurrentCallResourceNormalization GeneralRangeMapOrigins S05ConcreteProtectedChildCompletion
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

private theorem shared_held_tree (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (first second : Bool) (offset len : UInt64) (nonzero : len ≠ 0)
    (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat) :
    (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen first).tree =
    (tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen second).tree := by
  let rank := GeneralBorrowStructuralHistoryShared.depth tree runtime.formed.toState
  let slot := GeneralBorrowStructuralHistoryShared.slot tree runtime.formed.toState parent parentNode present room
  cases slot with
  | append noFree aligned fits =>
    let input : GeneralBorrowFreshMetadataChildShared.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        noFree,aligned,fits,first,offset,len,nonzero,runtime.formed.well,bounds⟩
    change GeneralBorrowFreshMetadataChildShared.result input = GeneralBorrowFreshMetadataChildShared.result {input with isProtected := second}
    rw [GeneralBorrowFreshMetadataChildShared.tree_eq,GeneralBorrowFreshMetadataChildShared.tree_eq]
    rfl
  | reuse child available bounded vacant slack =>
    let input : GeneralBorrowFreshMetadataChildSharedReuse.Input :=
      ⟨tree,rank,runtime.formed.children,runtime.formed.covered,parentTag,newTag,parent,parentNode,tagged,present,fresh,
        child,available,bounded,vacant,slack,first,offset,len,nonzero,runtime.formed.well,bounds⟩
    change GeneralBorrowFreshMetadataChildSharedReuse.result input = GeneralBorrowFreshMetadataChildSharedReuse.result {input with isProtected := second}
    rw [GeneralBorrowFreshMetadataChildSharedReuse.tree_eq,GeneralBorrowFreshMetadataChildSharedReuse.tree_eq]
    rfl

/-- A virtual protector view for a tag absent from this tree. This is only a
representation lemma; the actual release access still uses its original table. -/
private theorem absent_tag_view (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (allocation : AllocId) (tag : BorTag)
    (absent : ∀ index node, tree.nodeAt index = some node → node.tag ≠ tag) :
    DuplicatePrefixBorrowContract.RuntimeFacts tree (global.endCall (({} : FrameState).addProtector allocation tag)) := by
  have protectorEq : (global.endCall (({} : FrameState).addProtector allocation tag)).protectedTags = global.protectedTags.remove tag := by
    simp only [GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  refine ⟨⟨runtime.formed.toState,?_⟩,?_,runtime.possible,?_⟩
  · intro position valid
    rw [protectorEq]
    exact GeneralBorrowHiddenProtectorDropRuntime.profile tree _ _ _ (GeneralBorrowRelease.remove_weakens global.protectedTags tag)
      (runtime.formed.profile position valid)
  · intro position valid
    rw [protectorEq]
    apply GeneralBorrowProtectorCacheMap.remove_hidden tree _ global.protectedTags tag (runtime.coherent position valid)
    intro index node present tagged
    exact False.elim (absent index node present tagged)
  · refine ⟨runtime.below.mapping,?_⟩
    intro row member
    rw [protectorEq] at member
    exact runtime.below.protectors row (Array.mem_filter.mp member).1

/-- Actual protected Frozen construction retains old-source authority in the
computed post-removal view. No such authority is asserted under the live child
protector. Constructor trees coincide by their exact source equations. -/
theorem construct (tree : BorrowTree) (global : GlobalState) (completion : Completion)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (complete : ParentInterpretation tree completion)
    (allocation : AllocId) (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (nodeFresh : GeneralBorrowProtector.Fresh tree newTag)
    (room : tree.nodes.size+1 ≤ 4294967295) (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat)
    (source : UniIndex) (sourceLive : ∃ node, tree.nodes.get source = some node)
    (offset len : UInt64) (nonzero : len ≠ 0) (bounds : offset.toNat+len.toNat ≤ tree.locations.size.bytes.toNat)
    (owned : OwnedOn (S05CompletedAncestryReadMutable.Authority tree completion
      (global.endCall (({} : FrameState).addProtector allocation newTag)).protectedTags source)
      offset (offset+len) tree.locations) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen true
    ∃ child, actual.tree.indexOfTag newTag = some child ∧
      OwnedOn (S05CompletedAncestryReadMutable.Authority actual.tree (extend completion child parent)
        (global.endCall (({} : FrameState).addProtector allocation newTag)).protectedTags source)
        offset (offset+len) actual.tree.locations := by
  let future := global.endCall (({} : FrameState).addProtector allocation newTag)
  have futureRuntime : DuplicatePrefixBorrowContract.RuntimeFacts tree future := by
    apply absent_tag_view tree global runtime allocation newTag
    intro index node found
    exact nodeFresh (index,node) (Array.mem_toList_iff.mp
      ((GeneralBorrowFreshReuseProtection.entries_get tree.nodes index node).mpr found))
  have unheld : future.protectedTags.contains newTag = false := by
    change (global.protectedTags.remove newTag).contains newTag = false
    simp only [ProtectedTags.contains,ProtectedTags.get_remove_same,Option.isSome_none]
  obtain ⟨_,_,_,_,child,lookup,authority⟩ := CurrentCallOptionalSharedOldAuthority.construct tree future completion
    futureRuntime complete parentTag newTag parent parentNode tagged present fresh room tagBound unheld source sourceLive
    offset len nonzero bounds owned
  have same := shared_held_tree tree global runtime parentTag newTag parent parentNode tagged present fresh room true false offset len nonzero bounds
  refine ⟨child,?_,?_⟩
  · rw [same];exact lookup
  · rw [same];exact authority


end
end DuplicatePrefix.CurrentCallOptionalLenFuture
