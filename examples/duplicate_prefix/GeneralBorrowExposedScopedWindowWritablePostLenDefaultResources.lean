import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableSharedGlobal
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableSharedCallReady
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableSharedReleaseAllocator
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableSharedReleaseVacantClean
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableDefaultFromTargetRows
namespace DuplicatePrefix.GeneralBorrowExposedScopedWindowWritablePostLenDefaultResources
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open BorrowRangeAccess GeneralBorrowProjection GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedWindowWritableSharedPathMetadata (child)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option backward.split false

/-- Actual source len helper Read/construct/release/endCall forms the ordinary
mutable-expression input, allocator reserves, and physical vacancy from INITIAL
mixed resources and tag/cleanliness data. No final ownership/profile/cleanliness
or successful operation is an input. -/
theorem prepare (first helper : Input) (firstTags : ProtectedTags) (global : GlobalState)
    (allocation : AllocId) (selected head : UniIndex) (tail : List UniIndex)
    (firstRaw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources first firstTags selected head tail (fun _=>true))
    (helperRaw : GeneralBorrowExposedScopedWritableSharedConstructor.Resources helper global.protectedTags selected head tail
      (GeneralBorrowFreshMixedChild.extend (fun _=>true) (index first).toNat))
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
    ∃ data : GeneralBorrowExposedScopedWritableDefaultEntryRaw.Data released ended first.parentNode.tag future helper.offset helper.len selected head tail,
      data.input.parent=first.parent ∧ data.input.offset=helper.offset ∧ data.input.len=helper.len ∧
      GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (GeneralBorrowFreshMetadataChildDefault.index data.input)=none) data.input.tree.locations ∧
      GeneralBorrowGcVacantClean.VacantClean released ∧ GeneralBorrowGcAllocator.NodeTags released ∧
      released.nodes.size+2<65536 ∧ GeneralBorrowTagMap.Fresh released.tagMapping reserve
 := by
  let firstChild:=child first firstTags .VisitChildrenOfAccessed
  let helperChild:=child helper global.protectedTags .VisitChildrenOfAccessed
  let released:=(helperChild.releaseProtector helper.newTag global.protectedTags).tree
  have firstVacant:=GeneralBorrowExposedScopedWindowWritableSharedVacantClean.run first firstTags selected head tail (fun _=>true) firstRaw .VisitChildrenOfAccessed vacantClean
  have helperVacant : GeneralBorrowGcVacantClean.VacantClean helper.tree := by rw [treeEq];exact firstVacant
  have clean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index helper)=none) helper.tree.locations := by
    apply helperVacant
    unfold UniValMap.get
    rw [at_end helper]
    simp
  have firstMetadata:=GeneralBorrowExposedScopedWindowWritableSharedMetadata.run first firstTags selected head tail (fun _=>true) firstRaw initialTags
  have helperTags : GeneralBorrowGcAllocator.NodeTags helper.tree := by rw [treeEq];exact firstMetadata.1
  have helperMetadata:=GeneralBorrowExposedScopedWindowWritableSharedMetadata.run helper global.protectedTags selected head tail _ helperRaw helperTags
  obtain ⟨oldTarget,targetAtFirst,targetTag,targetExposure⟩:=firstMetadata.2.2.2.2 first.parent first.parentNode first.parentPresent
  have firstFrame:=GeneralBorrowStructuralReleaseGeometryFrame.release firstChild firstTags first.newTag
  change (firstChild.releaseProtector first.newTag firstTags).tree.nodeAt first.parent=some oldTarget at targetAtFirst
  have targetAtHelper : helper.tree.nodeAt first.parent=some oldTarget := by
    rw [firstFrame] at targetAtFirst
    rw [treeEq]
    exact targetAtFirst
  obtain ⟨targetNode,targetPresent,targetFinalTag,_⟩:=helperMetadata.2.2.2.2 first.parent oldTarget targetAtHelper
  obtain ⟨targetContext,targetWritable,writeData,readData⟩:=GeneralBorrowExposedScopedWindowWritableSharedCallReady.build first helper firstTags global allocation
    selected head tail firstRaw helperRaw treeEq parentEq initialTags exprUnheld positive clean
  have firstClean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index first)=none) first.tree.locations := by
    apply vacantClean
    unfold UniValMap.get
    rw [at_end first]
    simp
  have firstPositive : first.offset.toNat<(first.offset+first.len).toNat := by
    have bounds:=first.bounds
    have cap : first.tree.locations.size.bytes.toNat<2^64 := UInt64.toNat_lt_size _
    have nz : first.len.toNat≠0 := by intro zero;exact first.nonzero (UInt64.toNat_inj.mp zero)
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt (by omega : first.offset.toNat+first.len.toNat<2^64)]
    omega
  obtain ⟨firstAllocator⟩:=GeneralBorrowExposedScopedWindowWritableSharedReleaseAllocator.run first firstTags selected head tail (fun _=>true) firstRaw
    firstPositive
    firstClean future futureFresh firstDifferent
  have firstFrame:=GeneralBorrowStructuralReleaseGeometryFrame.release firstChild firstTags first.newTag
  have futureAtHelper : GeneralBorrowTagMap.Fresh helper.tree.tagMapping future := by
    have good:=firstAllocator.fresh
    change GeneralBorrowTagMap.Fresh (firstChild.releaseProtector first.newTag firstTags).tree.tagMapping future at good
    rw [firstFrame] at good
    rw [treeEq]
    exact good
  obtain ⟨allocator⟩:=GeneralBorrowExposedScopedWindowWritableSharedReleaseAllocator.run helper global.protectedTags selected head tail _ helperRaw positive clean future futureAtHelper helperDifferent
  obtain ⟨firstReserve⟩:=GeneralBorrowExposedScopedWindowWritableSharedReleaseAllocator.run first firstTags selected head tail (fun _=>true) firstRaw
    firstPositive
    firstClean reserve reserveFresh firstReserveDifferent
  have reserveAtHelper : GeneralBorrowTagMap.Fresh helper.tree.tagMapping reserve := by
    have good:=firstReserve.fresh
    change GeneralBorrowTagMap.Fresh (firstChild.releaseProtector first.newTag firstTags).tree.tagMapping reserve at good
    rw [firstFrame] at good
    rw [treeEq]
    exact good
  obtain ⟨reserveAllocator⟩:=GeneralBorrowExposedScopedWindowWritableSharedReleaseAllocator.run helper global.protectedTags selected head tail _ helperRaw positive clean reserve reserveAtHelper helperReserveDifferent
  have futureRoom : released.nodes.size+2<65536 := by
    rw [allocator.nodeSize]
    exact reserveRoom
  have boundsReleased : helper.offset.toNat+helper.len.toNat≤released.locations.size.bytes.toNat := by
    rw [allocator.capacity]
    exact helper.bounds
  have globals:=GeneralBorrowExposedScopedWindowWritableSharedGlobal.run helper global allocation selected head tail _ helperRaw positive clean helperTags
  have ready:=GeneralBorrowExposedScopedWindowWritableDefaultFromTargetRows.build released
    (global.endCall (({} : FrameState).addProtector allocation helper.newTag)).protectedTags first.parent selected head tail
    (fun position=>helperRaw.component.support position ∨ position=(index helper).toNat) targetContext targetNode targetPresent helperMetadata.2.1
    helper.offset helper.len helper.nonzero boundsReleased allocator.well targetWritable globals
    allocator.certificates allocator.noFree allocator.aligned future allocator.fresh futureRoom helperRaw.first helperRaw.rest
  rw [targetFinalTag,targetTag] at ready
  obtain ⟨data,parent,offsetEq,lenEq⟩:=ready
  have vacantResult:=GeneralBorrowExposedScopedWindowWritableSharedReleaseVacantClean.run helper global.protectedTags selected head tail _ helperRaw positive helperVacant
  refine ⟨data,parent,offsetEq,lenEq,?_,vacantResult,helperMetadata.2.1,futureRoom,reserveAllocator.fresh⟩
  have vacantInput : GeneralBorrowGcVacantClean.VacantClean data.input.tree := by
    rw [data.treeEq]
    exact vacantResult
  apply vacantInput
  unfold UniValMap.get
  rw [GeneralBorrowFreshMetadataChildDefault.at_end data.input]
  simp
end DuplicatePrefix.GeneralBorrowExposedScopedWindowWritablePostLenDefaultResources
