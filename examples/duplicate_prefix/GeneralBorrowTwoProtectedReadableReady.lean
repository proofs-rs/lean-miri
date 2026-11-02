import duplicate_prefix.GeneralBorrowProtectedLifetimeSeed
import duplicate_prefix.GeneralBorrowProtectedNextInput
import duplicate_prefix.GeneralBorrowProtectedReadReleaseExposed
import duplicate_prefix.GeneralBorrowRootExposureFrame
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableOld
namespace DuplicatePrefix.GeneralBorrowTwoProtectedReadableReady
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowProtectedReadRelease (Profile)
open DuplicatePrefix.GeneralBorrowProtectedLifetimeSeed
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

/-- Internally generated states immediately before the two chronological source
releases. Every operation starts from the real root allocation and constructor. -/
structure Ready where
  first : GeneralBorrowForestFnEntry.Output
  exposed : BorrowTree.TreeMutationResult
  second : GeneralBorrowForestFnEntry.Output
  firstEq : GeneralBorrowForestFnEntry.operation initial global {} allocation BorTag.one 0 1 .VisitChildrenOfAccessed = .ok first
  exposedEq : first.child.tree.exposeTag first.global.protectedTags first.tag = exposed
  secondEq : GeneralBorrowForestFnEntry.operation exposed.tree first.global first.frame allocation BorTag.one 0 1 .VisitChildrenOfAccessed = .ok second
  firstRead : first.access.status = .Completed
  firstChild : first.child.outcome = .ok ()
  exposedOK : exposed.outcome = .ok ()
  secondRead : second.access.status = .Completed
  secondChild : second.child.outcome = .ok ()
  firstTag : first.tag = tag2
  secondTag : second.tag = tag3
  tags : second.global.protectedTags = (({} : ProtectedTags).insert tag2 .StrongProtector).insert tag3 .StrongProtector
  frame : second.frame.protectedTags = #[(allocation,tag2),(allocation,tag3)]
  firstIndex : UniIndex
  secondIndex : UniIndex
  firstNode : TreeNode
  secondNode : TreeNode
  firstPresent : second.child.tree.nodeAt firstIndex = some firstNode
  secondPresent : second.child.tree.nodeAt secondIndex = some secondNode
  firstLookup : second.child.tree.indexOfTag tag2 = some firstIndex
  secondLookup : second.child.tree.indexOfTag tag3 = some secondIndex
  firstNodeTag : firstNode.tag = tag2
  secondNodeTag : secondNode.tag = tag3
  depth : ParentDepth second.child.tree.nodes
  children : GeneralBorrowGraph.ChildNodes second.child.tree
  covered : GeneralBorrowGraph.RootsCover second.child.tree
  roots : second.child.tree.roots = #[GeneralBorrowFullSharedSeed.root]
  fits : second.child.tree.nodes.data.size ≤ 4294967296
  profile : Every (Profile second.child.tree second.global.protectedTags) second.child.tree.locations

/-- Two overlapping protected Default constructors are generated internally,
with real fresh tag consumption, chronological registration and first-child
exposure before the second leading Read. No intermediate State or success is
assumed. This finite one-byte protocol is a BorrowTree lifecycle component. -/
theorem generate : Nonempty Ready := by
  have room : global.nextPointerTag.value < 18446744073709551615 := by decide
  have cleanFirst := clean (GeneralBorrowFreshMetadataChildMutable.index input) (by decide)
  obtain ⟨first,firstEq,firstTag,firstNext,firstHeld,firstFrame,firstRead,firstChild,firstProfile,⟨prepared⟩,firstTags,firstAccessEq,firstChildEq⟩ :=
    GeneralBorrowProtectedReadableFnEntry.invoke input global {} allocation rfl room rfl nodeTags rfl profile cleanFirst
  have firstTag2 : first.tag = tag2 := firstTag
  have firstNext3 : first.global.nextPointerTag = tag3 := firstNext
  have firstTags2 : first.global.protectedTags = ({} : ProtectedTags).insert tag2 .StrongProtector := firstTags
  have firstFrame2 : first.frame.protectedTags = #[(allocation,tag2)] := by simpa [firstTag2] using firstFrame
  have readFrame : (GeneralBorrowProtectedReadableStage.read input first.global.protectedTags).tree =
      {initial with locations := (GeneralBorrowProtectedReadableStage.read input first.global.protectedTags).tree.locations} :=
    GeneralBorrowFreshReadFrame.frame initial (.concrete BorTag.one) (Size.ofBytes 0) (Size.ofBytes 1) .Read first.global.protectedTags .VisitChildrenOfAccessed
  have readMapping : prepared.next.tree.tagMapping = initial.tagMapping := by
    rw [prepared.tree,readFrame]
  have readNodes : prepared.next.tree.nodes = initial.nodes := by
    rw [prepared.tree,readFrame]
  have fresh3 : GeneralBorrowTagMap.Fresh prepared.next.tree.tagMapping tag3 := by
    rw [readMapping]
    intro row member
    change row ∈ #[(BorTag.one,GeneralBorrowFullSharedSeed.root)] at member
    have same := Array.mem_singleton.mp member
    subst row
    decide
  have different : prepared.next.newTag ≠ tag3 := by rw [prepared.tag];change tag2 ≠ tag3;decide
  have nodeRoom : prepared.next.tree.tagMapping.mapping.size+1 ≤ 4294967295 := by rw [readMapping];decide
  let reserve := GeneralBorrowProtectedNextInput.after prepared.next tag3 fresh3 different nodeRoom
  have reserveTree : reserve.tree = GeneralBorrowFreshMetadataChildMutable.result prepared.next := by rfl
  have treeFirst : GeneralBorrowFreshMetadataChildMutable.result prepared.next = first.child.tree :=
    prepared.result.trans (congrArg BorrowTree.ChildInsertResult.tree firstChildEq.symm)
  let metadata := GeneralBorrowFreshMetadataChildMutable.append prepared.next
  obtain ⟨firstNode,firstPresent,firstNodeTag,parent,children,permission,unexposed⟩ := metadata.newNode
  have firstLookup : (GeneralBorrowFreshMetadataChildMutable.result prepared.next).indexOfTag tag2 =
      some (GeneralBorrowFreshMetadataChildMutable.index prepared.next) := by
    have lookup := metadata.freshLookup
    rw [prepared.tag] at lookup
    exact lookup
  have firstNodeTag2 : firstNode.tag = tag2 := firstNodeTag.trans prepared.tag
  let exposed := first.child.tree.exposeTag first.global.protectedTags first.tag
  have exposure := GeneralBorrowRootExposureFrame.expose (GeneralBorrowFreshMetadataChildMutable.result prepared.next) tag2
    (GeneralBorrowFreshMetadataChildMutable.index prepared.next) firstNode firstLookup firstPresent metadata.certificates.depth unexposed first.global.protectedTags
  have exposeEq : (GeneralBorrowFreshMetadataChildMutable.result prepared.next).exposeTag first.global.protectedTags tag2 = exposed := by
    rw [treeFirst]
    change first.child.tree.exposeTag first.global.protectedTags tag2 = first.child.tree.exposeTag first.global.protectedTags first.tag
    rw [firstTag2]
  rw [exposeEq] at exposure
  let secondInput := GeneralBorrowProtectedNextInput.shape_input reserve exposed.tree exposure.2.1
  have secondTagInput : secondInput.newTag = tag3 := rfl
  have secondParent : secondInput.parent = GeneralBorrowFullSharedSeed.root := prepared.parent
  have secondParentTag : secondInput.parentTag = BorTag.one := prepared.parentTag
  have secondOffset : secondInput.offset = 0 := prepared.offset
  have secondLen : secondInput.len = 1 := prepared.len
  have secondProfile : Every (Profile secondInput.tree first.global.protectedTags) secondInput.tree.locations := by
    apply GeneralBorrowProtectedReadProfileShape.shape reserve.tree exposed.tree first.global.protectedTags exposure.2.1
    rw [reserveTree,treeFirst]
    exact firstProfile
  have allocatorRead : GeneralBorrowGcAllocator.Invariant prepared.next.tree := by
    rw [prepared.tree,readFrame]
    let allocated := GeneralBorrowGcAllocator.initial BorTag.one (Size.ofBytes 1)
    exact ⟨allocated.pool,allocated.accounting,allocated.unique,allocated.nodeTags⟩
  have allocatorFirst := GeneralBorrowProtectedDefaultInvariant.Append.preserves prepared.next allocatorRead
  have secondNodeTags : ∀ index node,secondInput.tree.nodeAt index = some node → secondInput.tree.indexOfTag node.tag = some index :=
    GeneralBorrowSharedAllocatorInvariant.shape_tags reserve.tree exposed.tree exposure.2.1 allocatorFirst.nodeTags
  have secondRoots : secondInput.tree.roots = #[secondInput.parent] := by
    have roots := congrArg (fun row => row.2.2.2) exposure.2.1
    change exposed.tree.roots = reserve.tree.roots at roots
    change exposed.tree.roots = #[prepared.next.parent]
    rw [roots,reserveTree,metadata.roots,prepared.tree,readFrame,prepared.parent]
    rfl
  let query := GeneralBorrowFreshMetadataChildMutable.index secondInput
  have queryNat : query.toNat = 2 := by
    have atEnd := GeneralBorrowFreshMetadataChildMutable.at_end secondInput
    have sizes := congrArg (fun row => row.2.1) exposure.2.1
    have nodeSizes : exposed.tree.nodes.data.size = reserve.tree.nodes.data.size := by
      rw [reserveTree]
      simpa only [GeneralBorrowView.treeShape,Array.size_map] using congrArg Array.size sizes
    change query.toNat = exposed.tree.nodes.data.size at atEnd
    rw [nodeSizes,reserveTree] at atEnd
    change query.toNat = (GeneralBorrowFreshMetadataChildMutable.result prepared.next).nodes.size at atEnd
    rw [metadata.size,readNodes] at atEnd
    exact atEnd
  have beforeClean := clean query (by omega)
  have protectFresh : GeneralBorrowProtector.Fresh initial tag2 := by
    intro row member
    have present := (GeneralBorrowFreshReuseProtection.entries_get initial.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
    have lookup := nodeTags row.1 row.2 present
    intro same
    rw [same] at lookup
    have absent : initial.indexOfTag tag2 = none := by rfl
    rw [absent] at lookup;cases lookup
  have registeredProfile : Every (Profile initial first.global.protectedTags) initial.locations := by
    rw [firstTags2]
    intro position valid
    unfold Profile GeneralBorrowProtectedReadInvariantLocation.Data
    rw [GeneralBorrowProtector.normal_projection initial _ {} tag2 .StrongProtector protectFresh]
    exact profile position valid
  have readClean := GeneralBorrowProtectedReadRangeClean.preserves initial first.global.protectedTags BorTag.one
    GeneralBorrowFullSharedSeed.root GeneralBorrowFullSharedSeed.root (Size.ofBytes 0) (Size.ofBytes 1) .VisitChildrenOfAccessed
    query (by change 1 ≤ query.toNat;omega) beforeClean (by decide) input.depth input.children input.parentNode input.parentPresent
    rfl input.covered input.parentTagPresent input.well registeredProfile input.bounds
  have cleanRead : GeneralBorrowFreshFutureClean.Clean prepared.next.tree query := by
    rw [prepared.tree]
    intro position valid
    exact (readClean.2 position valid).2
  have notFirst : query ≠ GeneralBorrowFreshMetadataChildMutable.index prepared.next := by
    intro same
    have old := GeneralBorrowFreshMetadataChildMutable.at_end prepared.next
    rw [readNodes] at old
    have equality := congrArg UniIndex.toNat same
    rw [queryNat,old] at equality
    cases equality
  have cleanReserved := GeneralBorrowProtectedNextInput.future_clean prepared.next query notFirst cleanRead
  have secondClean : Every (fun location : LocationTree => location.perms.get query = none) secondInput.tree.locations :=
    GeneralBorrowFreshFutureClean.shape_preserves reserve.tree exposed.tree exposure.2.1 query cleanReserved
  have secondUnheld : first.global.protectedTags.get secondInput.newTag = none := by
    rw [secondTagInput,firstTags2]
    decide +kernel
  obtain ⟨second,secondEq,secondTag,secondNext,secondHeld,secondFrame,secondRead,secondChild,secondProfileAfter,⟨prepared2⟩,secondTags,secondAccessEq,secondChildEq⟩ :=
    GeneralBorrowProtectedReadableFnEntry.invoke secondInput first.global first.frame allocation
      (secondTagInput.trans firstNext3.symm) (by rw [firstNext3];decide) secondUnheld secondNodeTags secondRoots secondProfile secondClean
  have secondTag3 : second.tag = tag3 := secondTag.trans firstNext3
  have finalTags : second.global.protectedTags = (({} : ProtectedTags).insert tag2 .StrongProtector).insert tag3 .StrongProtector := by
    rw [secondTags,firstTags2,secondTagInput]
  have finalFrame : second.frame.protectedTags = #[(allocation,tag2),(allocation,tag3)] := by
    rw [secondFrame,firstFrame2,secondTag3]
    rfl
  rw [secondParentTag,secondOffset,secondLen] at secondEq
  have treeSecond : GeneralBorrowFreshMetadataChildMutable.result prepared2.next = second.child.tree :=
    prepared2.result.trans (congrArg BorrowTree.ChildInsertResult.tree secondChildEq.symm)
  let metadata2 := GeneralBorrowFreshMetadataChildMutable.append prepared2.next
  obtain ⟨secondNode,secondPresent,secondNodeTag,_,_,_,_⟩ := metadata2.newNode
  have secondLookup : second.child.tree.indexOfTag tag3 = some (GeneralBorrowFreshMetadataChildMutable.index prepared2.next) := by
    rw [←treeSecond]
    have lookup := metadata2.freshLookup
    rw [prepared2.tag,secondTagInput] at lookup
    exact lookup
  have secondNodeTag3 : secondNode.tag = tag3 := secondNodeTag.trans (prepared2.tag.trans secondTagInput)
  have readFrame2 : (GeneralBorrowProtectedReadableStage.read secondInput second.global.protectedTags).tree =
      {secondInput.tree with locations := (GeneralBorrowProtectedReadableStage.read secondInput second.global.protectedTags).tree.locations} :=
    GeneralBorrowFreshReadFrame.frame secondInput.tree (.concrete secondInput.parentTag) (Size.ofBytes secondInput.offset) (Size.ofBytes secondInput.len)
      .Read second.global.protectedTags .VisitChildrenOfAccessed
  have readNode2 : prepared2.next.tree.nodes = exposed.tree.nodes := by rw [prepared2.tree,readFrame2];rfl
  have readMap2 : prepared2.next.tree.tagMapping = exposed.tree.tagMapping := by rw [prepared2.tree,readFrame2];rfl
  have exposedFirst : exposed.tree.nodeAt (GeneralBorrowFreshMetadataChildMutable.index prepared.next) =
      some {firstNode with isExposed := true} := by
    change exposed.tree.nodes.get _ = _
    rw [exposure.2.2]
    exact GeneralBorrowFreshLocation.get_same _ _ _
  have firstBefore2 : prepared2.next.tree.nodeAt (GeneralBorrowFreshMetadataChildMutable.index prepared.next) =
      some {firstNode with isExposed := true} := by
    change prepared2.next.tree.nodes.get _ = _
    rw [readNode2]
    exact exposedFirst
  obtain ⟨firstFinal,firstFinalPresent,firstFinalTag,firstFinalFlag⟩ := GeneralBorrowFreshMetadataChildMutableOld.append prepared2.next
    (GeneralBorrowFreshMetadataChildMutable.index prepared.next) _ firstBefore2
  have exposedMapping : exposed.tree.tagMapping = reserve.tree.tagMapping := congrArg Prod.fst exposure.2.1
  have firstLookup2 : second.child.tree.indexOfTag tag2 = some (GeneralBorrowFreshMetadataChildMutable.index prepared.next) := by
    rw [←treeSecond]
    have distinct : prepared2.next.newTag ≠ tag2 := by rw [prepared2.tag,secondTagInput];decide
    rw [metadata2.oldLookup tag2 distinct]
    change prepared2.next.tree.tagMapping.get tag2 = _
    rw [readMap2,exposedMapping]
    exact firstLookup
  have finalRoots : second.child.tree.roots = #[GeneralBorrowFullSharedSeed.root] := by
    rw [←treeSecond,metadata2.roots,prepared2.tree,readFrame2]
    simpa only [secondParent] using secondRoots
  have finalFits : second.child.tree.nodes.data.size ≤ 4294967296 := by
    rw [←treeSecond]
    change (GeneralBorrowFreshMetadataChildMutable.result prepared2.next).nodes.size ≤ _
    rw [metadata2.size]
    change prepared2.next.tree.nodes.data.size+1 ≤ 4294967296
    have aligned := prepared2.next.aligned
    have fits := prepared2.next.fits
    omega
  refine ⟨⟨first,exposed,second,firstEq,rfl,secondEq,firstRead,firstChild,exposure.1,secondRead,secondChild,
    firstTag2,secondTag3,finalTags,finalFrame,_,_,firstFinal,secondNode,?_,?_,firstLookup2,secondLookup,
    firstFinalTag.trans firstNodeTag2,secondNodeTag3,?_,?_,?_,finalRoots,finalFits,secondProfileAfter⟩⟩
  · rw [←treeSecond];exact firstFinalPresent
  · rw [←treeSecond];exact secondPresent
  · rw [←treeSecond];exact metadata2.certificates.depth
  · rw [←treeSecond];exact metadata2.certificates.children
  · rw [←treeSecond];exact metadata2.certificates.covered
end DuplicatePrefix.GeneralBorrowTwoProtectedReadableReady
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowTwoProtectedReadableReady.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated two protected readable dependency {dependency}"
