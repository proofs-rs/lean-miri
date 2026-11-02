import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoSeed
import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoFullRange
import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoConflict
import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoEdges
import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoExposure
import duplicate_prefix.GeneralBorrowTwoProtectedReadableReady
import duplicate_prefix.GeneralBorrowTwoProtectedCacheReadyStage
import duplicate_prefix.GeneralBorrowExposureAllocation
import duplicate_prefix.GeneralBorrowPartitionExposeCardinality
import duplicate_prefix.GeneralBorrowProtectorCacheMap
import duplicate_prefix.GeneralBorrowProtectedLifetimeSeed
import duplicate_prefix.GeneralBorrowProtectedNextInput
import duplicate_prefix.GeneralBorrowProtectedReadReleaseExposed
import duplicate_prefix.GeneralBorrowRootExposureFrame
import duplicate_prefix.GeneralBorrowFreshMetadataChildMutableOld
namespace DuplicatePrefix.GeneralBorrowTwoProtectedCacheReady
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralRangeMapState DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralBorrowExposure
open DuplicatePrefix.GeneralBorrowProtectedReadRelease (Profile)
open DuplicatePrefix.GeneralBorrowProtectedLifetimeSeed
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000

structure Ready extends GeneralBorrowTwoProtectedReadableReady.Ready where
  coherent : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent second.child.tree location second.global.protectedTags) second.child.tree.locations
  nodeTags : ∀ index node,second.child.tree.nodeAt index = some node → second.child.tree.indexOfTag node.tag = some index
  onlyExposed : GeneralBorrowTwoProtectedStateInfoExposure.OnlyTag second.child.tree tag2
  firstConflicted : Every (GeneralBorrowConstructorPriorPermission.At firstIndex (some (.ReservedFrz true))) second.child.tree.locations

/-- Two overlapping protected Default constructors are generated internally,
with real fresh tag consumption, chronological registration and first-child
exposure before the second leading Read. No intermediate State or success is
assumed. This finite one-byte protocol is a BorrowTree lifecycle component. -/
theorem generate : Nonempty Ready := by
  have room : global.nextPointerTag.value < 18446744073709551615 := by decide
  have cleanFirst := clean (GeneralBorrowFreshMetadataChildMutable.index input) (by decide)
  obtain ⟨first,firstEq,firstTag,firstNext,firstHeld,firstFrame,firstRead,firstChild,firstProfile,⟨prepared⟩,firstTags,firstAccessEq,firstChildEq⟩ :=
    GeneralBorrowProtectedReadableFnEntry.invoke input global {} allocation rfl room rfl nodeTags rfl profile cleanFirst
  have firstRegisteredCache : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent initial location first.global.protectedTags) initial.locations := by
    rw [firstTags]
    exact GeneralBorrowProtectorCacheMap.register_fresh_global initial global {} allocation input.newTag .StrongProtector
      input.fresh nodeTags (GeneralBorrowExposureAllocation.coherent 1 BorTag.one global.protectedTags)
  have firstRegisteredProfile : Every (Profile initial first.global.protectedTags) initial.locations := by
    have fresh : GeneralBorrowProtector.Fresh initial input.newTag := by
      intro row member same
      have present := (GeneralBorrowFreshReuseProtection.entries_get initial.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
      have lookup := nodeTags row.1 row.2 present
      rw [same] at lookup
      have absent : initial.indexOfTag input.newTag = none := by rfl
      rw [absent] at lookup;cases lookup
    rw [firstTags]
    intro position valid
    change Nonempty (GeneralBorrowForest.Forest (source_normal_projection initial _ (global.protectedTags.insert input.newTag .StrongProtector)).topology) ∧
      GeneralBorrowProtectedReadInvariant.Data (source_normal_projection initial _ (global.protectedTags.insert input.newTag .StrongProtector))
    rw [GeneralBorrowProtector.normal_projection initial _ global.protectedTags input.newTag .StrongProtector fresh]
    exact profile position valid
  have firstCache : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent first.child.tree location first.global.protectedTags) first.child.tree.locations := by
    have cache := GeneralBorrowTwoProtectedCacheReadyStage.cache input first.global.protectedTags rfl firstRegisteredProfile firstRegisteredCache prepared
    rw [←firstChildEq] at cache
    exact cache
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
  have exposedCache := GeneralBorrowPartitionExposeCardinality.unexposed
    (GeneralBorrowFreshMetadataChildMutable.result prepared.next) first.global.protectedTags
    (GeneralBorrowFreshMetadataChildMutable.index prepared.next) firstNode firstPresent
    (by rw [firstNodeTag2];exact firstLookup) metadata.certificates.depth unexposed (by rw [treeFirst];exact firstCache)
  have exposedCoherent : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent exposed.tree location first.global.protectedTags) exposed.tree.locations := by
    have cache := exposedCache.2.1
    rw [firstNodeTag2,exposeEq] at cache
    exact cache
  have firstHeldTag : first.global.protectedTags.contains tag2 = true := by rw [firstTags2];simp [ProtectedTags.contains]
  have firstState := GeneralBorrowTwoProtectedStateInfoSeed.first_constructor_profile first.global.protectedTags prepared firstHeldTag
  have exposedPhysical : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile exposed.tree location first.global.protectedTags) exposed.tree.locations := by
    have exposedState := GeneralBorrowTwoProtectedStateInfoConflict.expose_profile
      (GeneralBorrowFreshMetadataChildMutable.result prepared.next) first.global.protectedTags
      (GeneralBorrowFreshMetadataChildMutable.index prepared.next) firstNode firstPresent
      (by rw [firstNodeTag2];exact firstLookup) metadata.certificates.depth firstState.1
    have state := exposedState.2
    rw [firstNodeTag2,exposeEq] at state
    exact state
  have exposedTyped := GeneralBorrowDefaultReservationType.shape_preserves reserve.tree exposed.tree exposure.2.1
    (GeneralBorrowFreshMetadataChildMutable.index prepared.next) firstState.2
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
  have secondRegisteredCache : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent secondInput.tree location second.global.protectedTags) secondInput.tree.locations := by
    rw [secondTags]
    exact GeneralBorrowProtectorCacheMap.register_fresh_global secondInput.tree first.global first.frame allocation secondInput.newTag .StrongProtector
      secondInput.fresh secondNodeTags exposedCoherent
  have secondRegisteredProfile : Every (Profile secondInput.tree second.global.protectedTags) secondInput.tree.locations := by
    have fresh : GeneralBorrowProtector.Fresh secondInput.tree secondInput.newTag := by
      intro row member same
      have present := (GeneralBorrowFreshReuseProtection.entries_get secondInput.tree.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
      have lookup := secondNodeTags row.1 row.2 present
      rw [same] at lookup
      have absent : secondInput.tree.indexOfTag secondInput.newTag = none := by
        simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find _ _ secondInput.fresh,Option.map_none]
      rw [absent] at lookup;cases lookup
    rw [secondTags]
    intro position valid
    change Nonempty (GeneralBorrowForest.Forest (source_normal_projection secondInput.tree _ (first.global.protectedTags.insert secondInput.newTag .StrongProtector)).topology) ∧
      GeneralBorrowProtectedReadInvariant.Data (source_normal_projection secondInput.tree _ (first.global.protectedTags.insert secondInput.newTag .StrongProtector))
    rw [GeneralBorrowProtector.normal_projection secondInput.tree _ first.global.protectedTags secondInput.newTag .StrongProtector fresh]
    exact secondProfile position valid
  have secondCache : Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent second.child.tree location second.global.protectedTags) second.child.tree.locations := by
    have cache := GeneralBorrowTwoProtectedCacheReadyStage.cache secondInput second.global.protectedTags secondRoots secondRegisteredProfile secondRegisteredCache prepared2
    rw [←secondChildEq] at cache
    exact cache
  have secondPhysical : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile secondInput.tree location second.global.protectedTags) secondInput.tree.locations := by
    rw [secondTags]
    exact GeneralBorrowSifaProtectionProfile.register secondInput.tree first.global first.frame allocation secondInput.newTag .StrongProtector
      secondInput.fresh secondNodeTags exposedPhysical
  have oldFirstPresent : secondInput.tree.nodeAt (GeneralBorrowFreshMetadataChildMutable.index prepared.next) = some {firstNode with isExposed := true} := by
    change exposed.tree.nodes.get _ = _
    rw [exposure.2.2]
    exact GeneralBorrowFreshLocation.get_same _ _ _
  have oldEdge : ({firstNode with isExposed := true} : TreeNode).parent = some secondInput.parent := by
    change firstNode.parent = some secondInput.parent
    rw [secondParent]
    have parentEq := parent
    rw [prepared.parent] at parentEq
    exact parentEq
  have edges := GeneralBorrowTwoProtectedStateInfoEdges.root_edges secondInput second.global.protectedTags secondRoots secondRegisteredProfile
    (GeneralBorrowFreshMetadataChildMutable.index prepared.next) _ oldFirstPresent oldEdge
  have firstHeldFinal : second.global.protectedTags.contains ({firstNode with isExposed := true} : TreeNode).tag = true := by
    change second.global.protectedTags.contains firstNode.tag = true
    rw [firstNodeTag2,secondTags,firstTags2,secondTagInput]
    simp [ProtectedTags.contains,GeneralBorrowProtectorCacheMap.insert_other _ tag3 tag2 .StrongProtector (by decide)]
  have firstConflict := GeneralBorrowTwoProtectedStateInfoConflict.child_conflict secondInput second.global.protectedTags secondRoots edges.1
    (GeneralBorrowFreshMetadataChildMutable.index prepared.next) _ oldFirstPresent edges.2 firstHeldFinal secondRegisteredProfile secondPhysical exposedTyped
  have firstSize := GeneralBorrowTwoProtectedCacheReadyStage.geometry input first.global.protectedTags rfl firstRegisteredProfile firstRegisteredCache prepared
  have secondSize := GeneralBorrowTwoProtectedCacheReadyStage.geometry secondInput second.global.protectedTags secondRoots secondRegisteredProfile secondRegisteredCache prepared2
  have exposedSize := (GeneralBorrowFreshGeometry.shape_frame reserve.tree exposed.tree exposure.2.1 reserve.well).2
  have oneByte : (GeneralBorrowProtectedReadableStage.child secondInput second.global.protectedTags).tree.locations.size = Size.ofBytes 1 := by
    rw [secondSize.2]
    change exposed.tree.locations.size = Size.ofBytes 1
    rw [exposedSize,reserveTree,treeFirst,firstChildEq,firstSize.2]
    rfl
  have conflicted : Every (GeneralBorrowConstructorPriorPermission.At (GeneralBorrowFreshMetadataChildMutable.index prepared.next) (some (.ReservedFrz true))) second.child.tree.locations := by
    rw [secondChildEq]
    have all := GeneralBorrowTwoProtectedStateInfoFullRange.every _
      (GeneralBorrowConstructorPriorPermission.At (GeneralBorrowFreshMetadataChildMutable.index prepared.next) (some (.ReservedFrz true)))
      1 secondSize.1 oneByte (by simpa [secondOffset,secondLen] using firstConflict)
    exact all
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
  let baseReady : GeneralBorrowTwoProtectedReadableReady.Ready := by
    refine ⟨first,exposed,second,firstEq,rfl,secondEq,firstRead,firstChild,exposure.1,secondRead,secondChild,
      firstTag2,secondTag3,finalTags,finalFrame,_,_,firstFinal,secondNode,?_,?_,firstLookup2,secondLookup,
      firstFinalTag.trans firstNodeTag2,secondNodeTag3,?_,?_,?_,finalRoots,finalFits,secondProfileAfter⟩
    · rw [←treeSecond];exact firstFinalPresent
    · rw [←treeSecond];exact secondPresent
    · rw [←treeSecond];exact metadata2.certificates.depth
    · rw [←treeSecond];exact metadata2.certificates.children
    · rw [←treeSecond];exact metadata2.certificates.covered
  have seedOnly : GeneralBorrowTwoProtectedStateInfoExposure.OnlyTag initial tag2 := by
    intro index node present flag
    have bound := GeneralBorrowNodeUpdate.lookup_valid initial.nodes index node present
    have same : index = GeneralBorrowFullSharedSeed.root := GeneralBorrowNodeUpdate.index_injective _ _ (by change index.toNat < 1 at bound;change index.toNat=0;omega)
    subst index
    change some (GeneralBorrowFullSharedSeed.node BorTag.one) = some node at present
    cases present
    cases flag
  have firstReadOnly : GeneralBorrowTwoProtectedStateInfoExposure.OnlyTag prepared.next.tree tag2 := by
    rw [prepared.tree,readFrame]
    exact seedOnly
  have firstOnly := GeneralBorrowTwoProtectedStateInfoExposure.append prepared.next tag2 firstReadOnly
  have exposedOnly := GeneralBorrowTwoProtectedStateInfoExposure.mark _ exposed.tree tag2
    (GeneralBorrowFreshMetadataChildMutable.index prepared.next) firstNode exposure.2.2 firstNodeTag2 firstOnly
  have secondReadOnly : GeneralBorrowTwoProtectedStateInfoExposure.OnlyTag prepared2.next.tree tag2 := by
    intro index node present flag
    change prepared2.next.tree.nodes.get index = some node at present
    rw [readNode2] at present
    exact exposedOnly index node present flag
  have finalOnly : GeneralBorrowTwoProtectedStateInfoExposure.OnlyTag second.child.tree tag2 := by
    rw [←treeSecond]
    exact GeneralBorrowTwoProtectedStateInfoExposure.append prepared2.next tag2 secondReadOnly
  have allocatorRead2 : GeneralBorrowGcAllocator.Invariant prepared2.next.tree := by
    rw [prepared2.tree,readFrame2]
    exact ⟨GeneralBorrowFreshStagePool.shape_pool reserve.tree exposed.tree exposure.2.1 allocatorFirst.pool,
      GeneralBorrowFreshStagePool.shape_accounting reserve.tree exposed.tree exposure.2.1 allocatorFirst.accounting,
      by change GeneralBorrowGcAllocator.KeyUnique exposed.tree.tagMapping;rw [exposedMapping];exact allocatorFirst.unique,
      secondNodeTags⟩
  have allocatorSecond := GeneralBorrowProtectedDefaultInvariant.Append.preserves prepared2.next allocatorRead2
  refine ⟨{toReady := baseReady,coherent := secondCache,nodeTags := ?_,onlyExposed := finalOnly,firstConflicted := conflicted}⟩
  rw [←treeSecond]
  exact allocatorSecond.nodeTags
end DuplicatePrefix.GeneralBorrowTwoProtectedCacheReady
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.GeneralBorrowTwoProtectedReadableReady.").length != 1 then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved generated two protected readable dependency {dependency}"
