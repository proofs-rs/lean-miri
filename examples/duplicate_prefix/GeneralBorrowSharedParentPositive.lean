import duplicate_prefix.GeneralBorrowSharedReadMetadata
import duplicate_prefix.GeneralBorrowRowRootMetadata
import duplicate_prefix.GeneralBorrowSharedCallbacksCapabilities
namespace DuplicatePrefix.GeneralBorrowSharedParentPositive
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralBorrowSharedCallbacksData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual unprotected shared construction retains the full parent S01 Positive,
including the selected physical-root path and unchanged root-tag cutoff. -/
theorem construct (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (parentTag newTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : tree.indexOfTag parentTag = some parent) (present : tree.nodeAt parent = some parentNode)
    (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping newTag) (room : tree.nodes.size+1 ≤ 4294967295)
    (tagBound : newTag.value.toNat < global.nextPointerTag.value.toNat) (unprotected : global.protectedTags.contains newTag = false)
    (selected : UniIndex) (maximum : Option BorTag) (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags (some parent) (some selected) maximum offset len) :
    let actual := tree.newChild (Size.ofBytes offset) (.concrete parentTag) newTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshAnchor.sharedState) .Frozen false
    actual.outcome = .ok () ∧ DuplicatePrefixBorrowContract.RuntimeFacts actual.tree global ∧
    actual.tree.locations.size = tree.locations.size ∧ actual.tree.nodes.size ≤ tree.nodes.size+1 ∧
    ∃ child, actual.tree.indexOfTag newTag = some child ∧ actual.tree.roots = tree.roots ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive actual.tree global.protectedTags (some parent) (some selected) maximum offset len) := by
  obtain ⟨done,afterRuntime,capacity,growth,child,lookup,roots,capabilities⟩ :=
    GeneralBorrowSharedCallbacksCapabilities.construct tree global runtime parentTag newTag parent parentNode tagged present fresh room tagBound unprotected selected maximum offset len positive
  have nonzero : len ≠ 0 := by intro zero;have p:=positive.positive;rw [zero] at p;contradiction
  obtain ⟨metadataChild,metadataLookup,metadata⟩ := GeneralBorrowSharedReadMetadata.construct tree global runtime
    parentTag newTag parent parentNode tagged present fresh room false offset len nonzero positive.bounds
  have same : metadataChild = child := Option.some.inj (metadataLookup.symm.trans lookup)
  subst metadataChild
  have geometry := GeneralBorrowRowRootMetadata.after_attach_parent tree _ parent child selected maximum
    (GeneralBorrowRowRootMetadata.of_positive tree global.protectedTags parent selected maximum offset len runtime.formed.well positive)
    metadata.paths metadata.nodes
  obtain ⟨afterParent,afterParentPresent,_,_⟩ := metadata.nodes parent parentNode present
  obtain ⟨selectedNode,selectedPresent,cutoff⟩ := geometry.root
  refine ⟨done,afterRuntime,capacity,growth,child,lookup,roots,⟨{
    positive := positive.positive,bounds := ?_,sourcePresent := ?_,wildcardRoot := ?_,rows := ?_}⟩⟩
  · rw [capacity]
    exact positive.bounds
  · intro source same
    have equal : source = parent := Option.some.inj same.symm
    subst source
    exact ⟨afterParent,afterParentPresent⟩
  · intro impossible
    cases impossible
  · intro position valid positiveWindow start stop
    obtain ⟨both,callbacks⟩ := capabilities position valid positiveWindow start stop
    refine ⟨{wildcard := ?_,rootPath := ?_,rootPresent := ?_,cutoff := ?_,normal := ?_,callbacks := callbacks}⟩
    · intro impossible
      cases impossible
    · intro source same
      have equal : source = parent := Option.some.inj same.symm
      subst source
      exact geometry.path _ _
    · intro root same
      have equal : root = selected := Option.some.inj same.symm
      subst root
      exact ⟨selectedNode,selectedPresent⟩
    · simpa only [Option.bind_some,selectedPresent,Option.map_some] using cutoff
    · intro source same
      have equal : source = parent := Option.some.inj same.symm
      subst source
      exact both.1
end DuplicatePrefix.GeneralBorrowSharedParentPositive
