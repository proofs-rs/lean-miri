import duplicate_prefix.GeneralBorrowProtectedConstructorExposureCache
import duplicate_prefix.GeneralBorrowProtectedSiblingGenerationReadSifaRange
import duplicate_prefix.GeneralBorrowTwoProtectedStateInfoConflict
import duplicate_prefix.GeneralBorrowProtectedNextInput
import duplicate_prefix.GeneralBorrowProtectedReadableFnEntry
import duplicate_prefix.GeneralBorrowPartitionExposeCardinality
import duplicate_prefix.GeneralBorrowProtectedReadProfileShape
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationStep
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapState GeneralBorrowExposureCardinality GeneralBorrowExposure GeneralBorrowProjection
open GeneralBorrowProtectedReadRelease (Profile)
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def expose (tree : BorrowTree) (protections : ProtectedTags) (tag : BorTag) (selected : Bool) : BorrowTree.TreeMutationResult :=
  if selected then tree.exposeTag protections tag else ⟨tree,.ok ()⟩

structure Ready (before : GeneralBorrowFreshMetadataChildMutable.Input) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (selected : Bool) (future : BorTag) where
  output : GeneralBorrowForestFnEntry.Output
  mutation : BorrowTree.TreeMutationResult
  next : GeneralBorrowFreshMetadataChildMutable.Input
  prepared : GeneralBorrowProtectedReadableStage.Prepared before output.global.protectedTags
  invoked : GeneralBorrowForestFnEntry.operation before.tree global frame allocation before.parentTag before.offset before.len .VisitChildrenOfAccessed = .ok output
  outputTag : output.tag = before.newTag
  childEq : output.child = GeneralBorrowProtectedReadableStage.child before output.global.protectedTags
  registeredProfile : Every (Profile before.tree output.global.protectedTags) before.tree.locations
  registeredPhysical : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile before.tree location output.global.protectedTags) before.tree.locations
  mutated : mutation = expose output.child.tree output.global.protectedTags output.tag selected
  exposureOK : mutation.outcome = .ok ()
  nextTree : next.tree = mutation.tree
  nextTag : next.newTag = future
  globalNext : output.global.nextPointerTag = future
  globalTags : output.global.protectedTags = global.protectedTags.insert before.newTag .StrongProtector
  frameTags : output.frame.protectedTags = frame.protectedTags.push (allocation,before.newTag)
  parentTag : next.parentTag = before.parentTag
  parent : next.parent = before.parent
  offset : next.offset = before.offset
  len : next.len = before.len
  roots : next.tree.roots = #[next.parent]
  profile : Every (Profile next.tree output.global.protectedTags) next.tree.locations
  physical : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile next.tree location output.global.protectedTags) next.tree.locations
  coherent : Every (fun location => LocationCoherent next.tree location output.global.protectedTags) next.tree.locations
  allocator : GeneralBorrowGcAllocator.Invariant next.tree
  shape : GeneralBorrowView.treeShape next.tree = GeneralBorrowView.treeShape (GeneralBorrowFreshMetadataChildMutable.result prepared.next)
  typed : GeneralBorrowDefaultReservationType.TreeTyped next.tree (GeneralBorrowFreshMetadataChildMutable.index prepared.next)
  node : TreeNode
  present : next.tree.nodeAt (GeneralBorrowFreshMetadataChildMutable.index prepared.next) = some node
  tagged : node.tag = before.newTag
  nodeParent : node.parent = some before.parent
  leaf : node.children = #[]
  defaultPermission : node.defaultInitialPermission = .ReservedFrz false
  lookup : next.tree.indexOfTag before.newTag = some (GeneralBorrowFreshMetadataChildMutable.index prepared.next)
  mapping : next.tree.tagMapping.mapping = before.tree.tagMapping.mapping.push (before.newTag,GeneralBorrowFreshMetadataChildMutable.index prepared.next)
  growth : next.tree.nodes.size = before.tree.nodes.size+1
  capacity : next.tree.locations.size = before.tree.locations.size

theorem generate (input : GeneralBorrowFreshMetadataChildMutable.Input) (global : GlobalState) (frame : FrameState)
    (allocation : AllocId) (selected : Bool)
    (tag : input.newTag = global.nextPointerTag) (room : global.nextPointerTag.value < 18446744073709551615)
    (unheld : global.protectedTags.get input.newTag = none) (roots : input.tree.roots = #[input.parent])
    (profile : Every (Profile input.tree global.protectedTags) input.tree.locations)
    (physical : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location global.protectedTags) input.tree.locations)
    (coherent : Every (fun location => LocationCoherent input.tree location global.protectedTags) input.tree.locations)
    (allocator : GeneralBorrowGcAllocator.Invariant input.tree)
    (future : BorTag) (futureEq : future = TypedRetagEmpty.successorTag global.nextPointerTag room)
    (futureFresh : GeneralBorrowTagMap.Fresh input.tree.tagMapping future) (different : input.newTag ≠ future)
    (nodeRoom : input.tree.tagMapping.mapping.size+1 ≤ 4294967295) :
    Nonempty (Ready input global frame allocation selected future) := by
  have vacant : input.tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index input) = none := by
    simp [UniValMap.get,GeneralBorrowFreshMetadataChildMutable.at_end input]
  have clean : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index input) = none) input.tree.locations :=
    fun position valid => (physical position valid).vacant _ vacant
  obtain ⟨output,invoked,outputTag,nextTag,held,frameTags,readOK,childOK,postProfile,⟨prepared⟩,globalTags,readEq,childEq⟩ :=
    GeneralBorrowProtectedReadableFnEntry.invoke input global frame allocation tag room unheld allocator.nodeTags roots profile clean
  have outputTag' : output.tag = input.newTag := outputTag.trans tag.symm
  have fresh : GeneralBorrowProtector.Fresh input.tree input.newTag := by
    intro row member same
    have found := (GeneralBorrowFreshReuseProtection.entries_get input.tree.nodes row.1 row.2).mp (Array.mem_toList_iff.mpr member)
    have lookup := allocator.nodeTags row.1 row.2 found
    rw [same] at lookup
    have absent : input.tree.indexOfTag input.newTag = none := by simp [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find _ _ input.fresh]
    change input.tree.tagMapping.get input.newTag = none at absent
    rw [absent] at lookup;cases lookup
  have registeredProfile : Every (Profile input.tree output.global.protectedTags) input.tree.locations := by
    rw [globalTags]
    intro position valid
    change Nonempty (GeneralBorrowForest.Forest (source_normal_projection input.tree _ (global.protectedTags.insert input.newTag .StrongProtector)).topology) ∧
      GeneralBorrowProtectedReadInvariant.Data (source_normal_projection input.tree _ (global.protectedTags.insert input.newTag .StrongProtector))
    rw [GeneralBorrowProtector.normal_projection input.tree _ global.protectedTags input.newTag .StrongProtector fresh]
    exact profile position valid
  have registeredPhysical : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile input.tree location output.global.protectedTags) input.tree.locations := by
    rw [globalTags]
    exact GeneralBorrowSifaProtectionProfile.register input.tree global frame allocation input.newTag .StrongProtector input.fresh allocator.nodeTags physical
  have registeredCache : Every (fun location => LocationCoherent input.tree location output.global.protectedTags) input.tree.locations := by
    rw [globalTags]
    exact GeneralBorrowProtectorCacheMap.register_fresh_global input.tree global frame allocation input.newTag .StrongProtector input.fresh allocator.nodeTags coherent
  have fits : input.tree.nodes.data.size ≤ 4294967296 := by have a := input.aligned;have b := input.fits;omega
  have accessed := GeneralBorrowProtectedSiblingGenerationReadSifaRange.ranged input.tree output.global.protectedTags input.parentTag input.parent input.parent
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .VisitChildrenOfAccessed fits input.depth input.children input.parentNode input.parentPresent
    roots input.covered input.parentTagPresent input.well (fun position valid => ⟨registeredPhysical position valid,registeredCache position valid⟩)
    input.offset (input.offset+input.len) (by intro position valid positive low high;exact registeredProfile position valid) (Nat.le_refl _) (Nat.le_refl _) input.bounds
  have physicalRead : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile prepared.next.tree location output.global.protectedTags) prepared.next.tree.locations := by
    rw [prepared.tree]
    exact fun position valid => (accessed.2.1 position valid).1
  have cacheRead : Every (fun location => LocationCoherent prepared.next.tree location output.global.protectedTags) prepared.next.tree.locations := by
    rw [prepared.tree]
    exact fun position valid => (accessed.2.1 position valid).2
  have physicalChild := (GeneralBorrowPositiveConstructorSifaProfile.Protected.append prepared.next output.global.protectedTags
    (by rw [prepared.tag,←outputTag'];change (output.global.protectedTags.get output.tag).isSome=true;rw [held];rfl) physicalRead).2
  have cacheChild := (GeneralBorrowProtectedConstructorExposureCache.append prepared.next output.global.protectedTags cacheRead).2
  have readFrame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read output.global.protectedTags .VisitChildrenOfAccessed
  change (GeneralBorrowProtectedReadableStage.read input output.global.protectedTags).tree =
    {input.tree with locations := (GeneralBorrowProtectedReadableStage.read input output.global.protectedTags).tree.locations} at readFrame
  have readNodes : prepared.next.tree.nodes = input.tree.nodes := by rw [prepared.tree,readFrame]
  have readMapping : prepared.next.tree.tagMapping = input.tree.tagMapping := by rw [prepared.tree,readFrame]
  have readAllocator : GeneralBorrowGcAllocator.Invariant prepared.next.tree := by
    rw [prepared.tree,readFrame]
    exact ⟨allocator.pool,allocator.accounting,allocator.unique,allocator.nodeTags⟩
  have allocatorChild := GeneralBorrowProtectedDefaultInvariant.Append.preserves prepared.next readAllocator
  have vacantRead : prepared.next.tree.nodes.get (GeneralBorrowFreshMetadataChildMutable.index prepared.next) = none := by simp [UniValMap.get,GeneralBorrowFreshMetadataChildMutable.at_end prepared.next]
  have cleanRead : Every (fun location : LocationTree => location.perms.get (GeneralBorrowFreshMetadataChildMutable.index prepared.next) = none) prepared.next.tree.locations :=
    fun position valid => (physicalRead position valid).vacant _ vacantRead
  have typedChild := GeneralBorrowProtectedReservationType.Append.formed prepared.next cleanRead
  let metadata := GeneralBorrowFreshMetadataChildMutable.append prepared.next
  obtain ⟨node,present,tagged,parent,leaf,permission,hidden⟩ := metadata.newNode
  have resultEq : GeneralBorrowFreshMetadataChildMutable.result prepared.next = output.child.tree := prepared.result.trans (congrArg BorrowTree.ChildInsertResult.tree childEq.symm)
  let mutation := expose output.child.tree output.global.protectedTags output.tag selected
  have exposeFacts := GeneralBorrowRootExposureFrame.expose _ prepared.next.newTag (GeneralBorrowFreshMetadataChildMutable.index prepared.next) node metadata.freshLookup present metadata.certificates.depth hidden output.global.protectedTags
  have mutationShape : GeneralBorrowView.treeShape mutation.tree = GeneralBorrowView.treeShape (GeneralBorrowFreshMetadataChildMutable.result prepared.next) := by
    cases selected with
    | false => change GeneralBorrowView.treeShape output.child.tree = _;rw [resultEq]
    | true => change GeneralBorrowView.treeShape (output.child.tree.exposeTag output.global.protectedTags output.tag).tree = _
              rw [←resultEq,outputTag',←prepared.tag];exact exposeFacts.2.1
  have mutationOK : mutation.outcome = .ok () := by
    cases selected with
    | false => rfl
    | true => change (output.child.tree.exposeTag output.global.protectedTags output.tag).outcome = _
              rw [←resultEq,outputTag',←prepared.tag];exact exposeFacts.1
  have mutatedPhysical : Every (fun location => GeneralBorrowLocationSifaConsistency.Profile mutation.tree location output.global.protectedTags) mutation.tree.locations := by
    cases selected with
    | false =>
      change Every (fun location => GeneralBorrowLocationSifaConsistency.Profile output.child.tree location output.global.protectedTags) output.child.tree.locations
      rw [←resultEq];exact physicalChild
    | true =>
      change Every (fun location => GeneralBorrowLocationSifaConsistency.Profile (output.child.tree.exposeTag output.global.protectedTags output.tag).tree location output.global.protectedTags)
        (output.child.tree.exposeTag output.global.protectedTags output.tag).tree.locations
      rw [←resultEq,outputTag',←prepared.tag]
      have facts := (GeneralBorrowTwoProtectedStateInfoConflict.expose_profile _ _ _ node present (by rw [tagged];exact metadata.freshLookup) metadata.certificates.depth physicalChild).2
      simpa only [tagged,GeneralBorrowPartitionExposeCardinality.Coherent] using facts
  have mutatedCache : Every (fun location => LocationCoherent mutation.tree location output.global.protectedTags) mutation.tree.locations := by
    cases selected with
    | false =>
      change Every (fun location => LocationCoherent output.child.tree location output.global.protectedTags) output.child.tree.locations
      rw [←resultEq];exact cacheChild
    | true =>
      change Every (fun location => LocationCoherent (output.child.tree.exposeTag output.global.protectedTags output.tag).tree location output.global.protectedTags)
        (output.child.tree.exposeTag output.global.protectedTags output.tag).tree.locations
      rw [←resultEq,outputTag',←prepared.tag]
      have facts := (GeneralBorrowPartitionExposeCardinality.expose _ _ _ node present (by rw [tagged];exact metadata.freshLookup) metadata.certificates.depth cacheChild).2
      simpa only [tagged,GeneralBorrowPartitionExposeCardinality.Coherent] using facts
  have nextFresh : GeneralBorrowTagMap.Fresh prepared.next.tree.tagMapping future := by rw [readMapping];exact futureFresh
  have nextDifferent : prepared.next.newTag ≠ future := by rw [prepared.tag];exact different
  have nextRoom : prepared.next.tree.tagMapping.mapping.size+1 ≤ 4294967295 := by rw [readMapping];exact nodeRoom
  let reserve := GeneralBorrowProtectedNextInput.after prepared.next future nextFresh nextDifferent nextRoom
  let next := GeneralBorrowProtectedNextInput.shape_input reserve mutation.tree mutationShape
  obtain ⟨newNode,newPresent,newTag,newParent,newChildren,newPermission⟩ := GeneralBorrowFreshMetadata.node_fields _ mutation.tree mutationShape
    (GeneralBorrowFreshMetadataChildMutable.index prepared.next) node present
  have mutationMapping : mutation.tree.tagMapping = (GeneralBorrowFreshMetadataChildMutable.result prepared.next).tagMapping := congrArg Prod.fst mutationShape
  have finalAllocator : GeneralBorrowGcAllocator.Invariant next.tree := {
    pool := GeneralBorrowFreshStagePool.shape_pool _ _ mutationShape allocatorChild.pool
    accounting := GeneralBorrowFreshStagePool.shape_accounting _ _ mutationShape allocatorChild.accounting
    unique := by change GeneralBorrowGcAllocator.KeyUnique mutation.tree.tagMapping;rw [mutationMapping];exact allocatorChild.unique
    nodeTags := GeneralBorrowSharedAllocatorInvariant.shape_tags _ _ mutationShape allocatorChild.nodeTags }
  refine ⟨{
    output := output,mutation := mutation,next := next,prepared := prepared,invoked := invoked,outputTag := outputTag',childEq := childEq,registeredProfile := registeredProfile,registeredPhysical := registeredPhysical,mutated := rfl,
    exposureOK := mutationOK,nextTree := rfl,nextTag := rfl,globalNext := nextTag.trans futureEq.symm,globalTags := globalTags,
    frameTags := by rw [frameTags,outputTag'],
    parentTag := prepared.parentTag,parent := prepared.parent,offset := prepared.offset,len := prepared.len,
    roots := ?_,profile := ?_,physical := mutatedPhysical,coherent := mutatedCache,allocator := finalAllocator,shape := mutationShape,
    typed := GeneralBorrowDefaultReservationType.shape_preserves _ _ mutationShape _ typedChild,
    node := newNode,present := newPresent,tagged := newTag.trans (tagged.trans prepared.tag),nodeParent := newParent.trans (parent.trans (congrArg some prepared.parent)),
    leaf := newChildren.trans leaf,defaultPermission := newPermission.trans permission,lookup := ?_,mapping := ?_,growth := ?_,capacity := ?_}⟩
  · change mutation.tree.roots = #[prepared.next.parent]
    have rootFrame := congrArg (fun row => row.2.2.2) mutationShape
    change mutation.tree.roots = (GeneralBorrowFreshMetadataChildMutable.result prepared.next).roots at rootFrame
    rw [rootFrame,metadata.roots,prepared.tree,readFrame,prepared.parent]
    exact roots
  · exact GeneralBorrowProtectedReadProfileShape.shape _ _ output.global.protectedTags (by rw [resultEq] at mutationShape;exact mutationShape) postProfile
  · change mutation.tree.tagMapping.get input.newTag = _
    rw [mutationMapping]
    have lookup := metadata.freshLookup
    rw [prepared.tag] at lookup
    exact lookup
  · change mutation.tree.tagMapping.mapping = _
    rw [mutationMapping,metadata.mapping]
    simp only [GeneralBorrowFreshMetadataChildMutable.mapping,prepared.tag,readMapping]
  · have sizes := congrArg (fun row => row.2.1) mutationShape
    have count : mutation.tree.nodes.size = (GeneralBorrowFreshMetadataChildMutable.result prepared.next).nodes.size := by simpa only [GeneralBorrowView.treeShape,UniValMap.size,Array.size_map] using congrArg Array.size sizes
    change mutation.tree.nodes.size = _
    rw [count,metadata.size,readNodes]
  · have geometry := (GeneralBorrowFreshGeometry.shape_frame _ _ mutationShape (GeneralBorrowFreshMutableGeometry.append_frame prepared.next).1).2
    change mutation.tree.locations.size = _
    rw [geometry,(GeneralBorrowFreshMutableGeometry.append_frame prepared.next).2,prepared.tree]
    exact accessed.2.2.2.1
end DuplicatePrefix.GeneralBorrowProtectedSiblingGenerationStep
