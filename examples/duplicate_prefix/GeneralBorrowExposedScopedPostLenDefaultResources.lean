import duplicate_prefix.GeneralBorrowExposedScopedSharedCallWriteReady
import duplicate_prefix.GeneralBorrowExposedScopedSharedReleaseAllocator
import duplicate_prefix.GeneralBorrowExposedScopedSharedReleaseVacantClean
import duplicate_prefix.GeneralBorrowExposedScopedMutableEntryRaw
import duplicate_prefix.GeneralBorrowExposedScopedDefaultFromHelperRows
namespace DuplicatePrefix.GeneralBorrowExposedScopedPostLenDefaultResources
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedSharedPathMetadata (child)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option backward.split false

theorem full_every (predicate : α → Prop) (map : DedupRangeMap α) (well : map.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn predicate 0 map.size.bytes map) : GeneralRangeMapState.Every predicate map := by
  intro position valid
  have facts := GeneralRangeMapGeometry.facts map well (by omega)
  have lastValid : map.entries.size-1 < map.entries.size := by omega
  have lastPositive := facts.2.1 (map.entries.size-1) lastValid
  have lastSize := GeneralRangeMapGeometry.size_last map (by omega)
  have positive := facts.2.1 position valid
  have startBound : map.entries[position].range.start.toNat < map.size.bytes.toNat := by
    rw [lastSize]
    by_cases same : position = map.entries.size-1
    · subst position;exact lastPositive
    · have before : position < map.entries.size-1 := by omega
      have separation := GeneralRangeMapGeometry.stop_le_start map well position (map.entries.size-1) before lastValid
      omega
  exact owned position valid (by simp only [UInt64.toNat_zero];omega) startBound (by simp only [UInt64.toNat_zero];omega)


theorem prepare (first helper : Input) (firstTags : ProtectedTags) (global : GlobalState)
    (allocation : AllocId) (selected head : UniIndex) (tail : List UniIndex)
    (firstRaw : GeneralBorrowExposedScopedSharedLeafConstructor.Resources first firstTags selected head tail (fun _=>true))
    (helperRaw : GeneralBorrowExposedScopedSharedLeafConstructor.Resources helper global.protectedTags selected head tail
      (GeneralBorrowFreshMixedChild.extend (fun _=>true) (index first).toNat))
    (firstAtBase : first.offset=0) (firstFull : first.len=first.tree.locations.size.bytes)
    (helperAtBase : helper.offset=0) (helperFull : helper.len=helper.tree.locations.size.bytes)
    (treeEq : helper.tree=child first firstTags .VisitChildrenOfAccessed) (parentEq : helper.parent=index first)
    (initialTags : GeneralBorrowGcAllocator.NodeTags first.tree)
    (exprUnheld : global.protectedTags.contains helper.parentNode.tag=false)
    (positive : helper.offset.toNat<(helper.offset+helper.len).toNat)
    (vacantClean : GeneralBorrowGcVacantClean.VacantClean first.tree)
    (future reserve : BorTag)
    (futureFresh : GeneralBorrowTagMap.Fresh first.tree.tagMapping future)
    (reserveFresh : GeneralBorrowTagMap.Fresh first.tree.tagMapping reserve)
    (firstDifferent : first.newTag≠future) (helperDifferent : helper.newTag≠future)
    (firstReserveDifferent : first.newTag≠reserve) (helperReserveDifferent : helper.newTag≠reserve)
    (reserveRoom : helper.tree.nodes.size+3<65536) :
    let released:=((child helper global.protectedTags .VisitChildrenOfAccessed).releaseProtector helper.newTag global.protectedTags).tree
    let ended:=(global.endCall (({} : FrameState).addProtector allocation helper.newTag)).protectedTags
    ∃ data : GeneralBorrowExposedScopedMutableEntryRaw.Data released ended first.parentNode.tag future helper.offset helper.len selected head tail,
      data.input.parent=first.parent ∧ data.input.offset=0 ∧ data.input.len=data.input.tree.locations.size.bytes ∧
      GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (GeneralBorrowFreshMetadataChildDefault.index data.input)=none) data.input.tree.locations ∧
      GeneralBorrowGcVacantClean.VacantClean released ∧ GeneralBorrowGcAllocator.NodeTags released ∧
      released.nodes.size+2<65536 ∧ GeneralBorrowTagMap.Fresh released.tagMapping reserve
 := by
  let firstChild:=child first firstTags .VisitChildrenOfAccessed
  let helperChild:=child helper global.protectedTags .VisitChildrenOfAccessed
  let released:=(helperChild.releaseProtector helper.newTag global.protectedTags).tree
  have firstVacant:=GeneralBorrowExposedScopedSharedLeafVacantClean.run first firstTags selected head tail (fun _=>true) firstRaw firstAtBase firstFull .VisitChildrenOfAccessed vacantClean
  have helperVacant : GeneralBorrowGcVacantClean.VacantClean helper.tree := by rw [treeEq];exact firstVacant
  have clean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index helper)=none) helper.tree.locations := by
    apply helperVacant
    unfold UniValMap.get
    rw [at_end helper]
    simp
  have firstMetadata:=GeneralBorrowExposedScopedSharedMetadata.run first firstTags selected head tail (fun _=>true) firstRaw firstAtBase firstFull initialTags
  have helperTags : GeneralBorrowGcAllocator.NodeTags helper.tree := by rw [treeEq];exact firstMetadata.1
  have helperMetadata:=GeneralBorrowExposedScopedSharedMetadata.run helper global.protectedTags selected head tail _ helperRaw helperAtBase helperFull helperTags
  obtain ⟨oldTarget,targetAtFirst,targetTag,targetExposure⟩:=firstMetadata.2.2.2.2 first.parent first.parentNode first.parentPresent
  have firstFrame:=GeneralBorrowStructuralReleaseGeometryFrame.release firstChild firstTags first.newTag
  change (firstChild.releaseProtector first.newTag firstTags).tree.nodeAt first.parent=some oldTarget at targetAtFirst
  have targetAtHelper : helper.tree.nodeAt first.parent=some oldTarget := by
    rw [firstFrame] at targetAtFirst
    rw [treeEq]
    exact targetAtFirst
  obtain ⟨targetNode,targetPresent,targetFinalTag,_⟩:=helperMetadata.2.2.2.2 first.parent oldTarget targetAtHelper
  obtain ⟨exprNode,exprPresent,exprTag,_⟩:=helperMetadata.2.2.2.2 helper.parent helper.parentNode helper.parentPresent
  rw [parentEq] at exprPresent
  obtain ⟨helperNode,helperPresent,helperTag,helperHidden⟩:=helperMetadata.2.2.2.1
  obtain ⟨helperContext⟩:=GeneralBorrowExposedScopedSharedCallWriteReady.helper_context helper global selected head tail _ helperRaw helperAtBase helperFull
  have frame:=GeneralBorrowStructuralReleaseGeometryFrame.release helperChild global.protectedTags helper.newTag
  have paths (location : LocationTree) := GeneralBorrowExposedScopedSharedPathMetadata.two_step first helper firstTags global.protectedTags selected head tail (fun _=>true)
    firstRaw helperRaw firstAtBase firstFull helperAtBase helperFull .VisitChildrenOfAccessed .VisitChildrenOfAccessed treeEq parentEq global.protectedTags location
  have releasedPaths (location : LocationTree) :
      (source_normal_projection released location global.protectedTags).topology.ancestorPath (index helper).toNat=
        (index helper).toNat::(index first).toNat::(source_normal_projection released location global.protectedTags).topology.ancestorPath first.parent.toNat ∧
      (index first).toNat∉(source_normal_projection released location global.protectedTags).topology.ancestorPath first.parent.toNat ∧
      (index helper).toNat∉(source_normal_projection released location global.protectedTags).topology.ancestorPath first.parent.toNat := by
    dsimp only [released]
    rw [frame]
    exact paths location
  have unique:=GeneralBorrowExposedScopedSharedLeafReadReleaseUnique.release helper global.protectedTags selected head tail _ helperRaw helperAtBase helperFull positive clean
  have restored:=GeneralBorrowExposedScopedSharedUniqueWriteRestore.ranged released global allocation (index helper) (index first) first.parent selected head tail
    (fun position=>helperRaw.component.support position ∨ position=(index helper).toNat) helper.offset (helper.offset+helper.len) unique.2.1 helperContext
    targetNode exprNode helperNode targetPresent exprPresent helperPresent helperMetadata.2.1
    (by rw [exprTag];exact exprUnheld) (fun location=>(releasedPaths location).1)
    (fun location=>(releasedPaths location).2.1) (fun location=>(releasedPaths location).2.2) helperRaw.first helperRaw.rest
  rw [helperTag] at restored
  let targetContext : GeneralBorrowExposedKnownRootRangeData.Context released first.parent selected head tail:={
    helperContext with anchorNode:=targetNode,anchorPresent:=targetPresent }
  have firstClean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index first)=none) first.tree.locations := by
    apply vacantClean
    unfold UniValMap.get
    rw [at_end first]
    simp
  have firstPositive : first.offset.toNat<(first.offset+first.len).toNat := by
    rw [firstAtBase,UInt64.zero_add]
    change 0<first.len.toNat
    have nz : first.len.toNat≠0 := by
      intro zero
      exact first.nonzero (UInt64.toNat_inj.mp zero)
    omega
  obtain ⟨firstAllocator⟩:=GeneralBorrowExposedScopedSharedReleaseAllocator.run first firstTags selected head tail (fun _=>true) firstRaw firstAtBase firstFull
    firstPositive
    firstClean future futureFresh firstDifferent
  have firstFrame:=GeneralBorrowStructuralReleaseGeometryFrame.release firstChild firstTags first.newTag
  have futureAtHelper : GeneralBorrowTagMap.Fresh helper.tree.tagMapping future := by
    have good:=firstAllocator.fresh
    change GeneralBorrowTagMap.Fresh (firstChild.releaseProtector first.newTag firstTags).tree.tagMapping future at good
    rw [firstFrame] at good
    rw [treeEq]
    exact good
  obtain ⟨allocator⟩:=GeneralBorrowExposedScopedSharedReleaseAllocator.run helper global.protectedTags selected head tail _ helperRaw helperAtBase helperFull positive clean future futureAtHelper helperDifferent
  obtain ⟨firstReserve⟩:=GeneralBorrowExposedScopedSharedReleaseAllocator.run first firstTags selected head tail (fun _=>true) firstRaw firstAtBase firstFull
    firstPositive
    firstClean reserve reserveFresh firstReserveDifferent
  have reserveAtHelper : GeneralBorrowTagMap.Fresh helper.tree.tagMapping reserve := by
    have good:=firstReserve.fresh
    change GeneralBorrowTagMap.Fresh (firstChild.releaseProtector first.newTag firstTags).tree.tagMapping reserve at good
    rw [firstFrame] at good
    rw [treeEq]
    exact good
  obtain ⟨reserveAllocator⟩:=GeneralBorrowExposedScopedSharedReleaseAllocator.run helper global.protectedTags selected head tail _ helperRaw helperAtBase helperFull positive clean reserve reserveAtHelper helperReserveDifferent
  have futureRoom : released.nodes.size+2<65536 := by
    rw [allocator.nodeSize]
    exact reserveRoom
  have fullReleased : helper.len=released.locations.size.bytes :=
    helperFull.trans (congrArg Size.bytes allocator.capacity).symm
  have ready:=GeneralBorrowExposedScopedDefaultFromHelperRows.build released global allocation (index helper) (index first) first.parent selected head tail
    (fun position=>helperRaw.component.support position ∨ position=(index helper).toNat) helperContext targetNode exprNode helperNode
    targetPresent exprPresent helperPresent helperMetadata.2.1 (by rw [exprTag];exact exprUnheld)
    (fun location=>(releasedPaths location).1) (fun location=>(releasedPaths location).2.1) (fun location=>(releasedPaths location).2.2)
    helper.offset helper.len helper.nonzero helperAtBase fullReleased allocator.well unique.2.1
    allocator.certificates allocator.noFree allocator.aligned future allocator.fresh futureRoom helperRaw.first helperRaw.rest
  rw [helperTag,targetFinalTag,targetTag] at ready
  obtain ⟨data,parent,atBase,full⟩:=ready
  have vacantResult:=GeneralBorrowExposedScopedSharedReleaseVacantClean.run helper global.protectedTags selected head tail _ helperRaw helperAtBase helperFull positive helperVacant
  refine ⟨data,parent,atBase,full,?_,vacantResult,helperMetadata.2.1,futureRoom,reserveAllocator.fresh⟩
  have vacantInput : GeneralBorrowGcVacantClean.VacantClean data.input.tree := by
    rw [data.treeEq]
    exact vacantResult
  apply vacantInput
  unfold UniValMap.get
  rw [GeneralBorrowFreshMetadataChildDefault.at_end data.input]
  simp
end DuplicatePrefix.GeneralBorrowExposedScopedPostLenDefaultResources
