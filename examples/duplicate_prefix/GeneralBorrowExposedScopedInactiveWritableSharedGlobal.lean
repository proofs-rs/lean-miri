import duplicate_prefix.GeneralBorrowExposedScopedInactiveWindowWritableSharedGlobal
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedMetadata
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata
import duplicate_prefix.GeneralBorrowExposedScopedWritableOldFrame
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableCleanReadRange
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedConstructor
import duplicate_prefix.GeneralBorrowExposedScopedSharedActivity
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableReadReleaseGlobal
import duplicate_prefix.GeneralBorrowFreshSharedGeometry
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometry
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedGlobal
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess DuplicatePrefix.GeneralBorrowProjection
open GeneralBorrowFreshMetadataChildShared
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowExposedScopedInactiveWritableSharedConstructor (Resources)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- Real shared child formation and its real protector-end callbacks are joined
from initial resources and a clean allocator slot. Activity, child contracts,
release success and final partition geometry are all derived. -/
theorem construct_release (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input) = none) input.tree.locations) :
    let child := result input
    let released := child.releaseProtector input.newTag protections
    GeneralRangeMapState.Every (fun location=>GeneralBorrowExposureCardinality.LocationCoherent released.tree location protections ∧
      GeneralBorrowSifaWritableFrame.Profile released.tree protections area.support location ∧
      GeneralBorrowExposedInactiveConstructor.Profile released.tree location (index input) (fun position=>raw.component.support position∨position=(index input).toNat)) released.tree.locations := by
  let metadata := GeneralBorrowFreshMetadataChildShared.append input
  let child := result input
  obtain ⟨success,context,owned⟩ := GeneralBorrowExposedScopedInactiveWritableSharedConstructor.construct input protections selected head tail writable raw
  have geometry := GeneralBorrowFreshSharedGeometry.append_frame input
  have activity := GeneralBorrowExposedScopedSharedActivity.append input.tree input.depth input.parentTag input.newTag input.parent input.parentNode
    input.parentTagPresent input.parentPresent input.fresh input.noFree input.aligned input.fits input.isProtected input.offset input.len
    input.nonzero input.well input.bounds clean
  have active := GeneralBorrowFreshActiveWithin.active_on child (index input) .Read input.offset (input.offset+input.len) geometry.1 activity
  have fits : child.nodes.data.size ≤ 4294967296 := by
    change child.nodes.size ≤ 4294967296
    rw [metadata.size]
    have bound := raw.room
    omega
  have hidden : context.anchorNode.isExposed = false := by
    obtain ⟨node,present,tag,parent,children,permission,exposed⟩ := metadata.newNode
    have same := Option.some.inj (context.anchorPresent.symm.trans present)
    rw [same]
    exact exposed
  have cache:=GeneralBorrowSharedConstructorExposureCache.append input protections raw.coherent
  have profile:=GeneralBorrowExposedScopedWritableOldFrame.shared input protections area.support
    (by intro query included;obtain ⟨node,present,_,_⟩:=raw.leaves query included;exact ⟨node,present⟩)
    (by intro query included same;apply raw.separate query included;rw [same];exact raw.component.anchor)
    raw.writableLeaves
  have exposures:=GeneralBorrowExposedInactiveConstructor.shared input raw.component.support raw.forest raw.exposures
  have done := GeneralBorrowExposedScopedInactiveWritableReadReleaseGlobal.release child protections input.newTag (index input) selected head tail context
    (fun position => raw.component.support position ∨ position = (index input).toNat)
    (GeneralBorrowFreshMixedChild.extend writable (index input).toNat) input.offset (input.offset+input.len) positive fits hidden
    (by obtain ⟨node,present,tag,parent,children,permission,exposed⟩:=metadata.newNode;have same:=Option.some.inj (context.anchorPresent.symm.trans present);rw [same];exact children)
    metadata.freshLookup active owned (by intro position valid;exact ⟨cache.2 position valid,profile position valid,by
      intro query node member present exposed
      apply exposures position valid query node _ present exposed
      rcases member with old | fresh
      · exact Or.inr old
      · exact Or.inl fresh⟩)
  exact done.2.2

theorem held (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input protections selected head tail writable)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input)=none) input.tree.locations) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected
    let released := child.tree.releaseProtector input.newTag protections
    GeneralRangeMapState.Every (fun location=>GeneralBorrowExposureCardinality.LocationCoherent released.tree location protections ∧
      GeneralBorrowSifaWritableFrame.Profile released.tree protections area.support location ∧
      GeneralBorrowExposedInactiveConstructor.Profile released.tree location (index input) (fun position=>raw.component.support position∨position=(index input).toNat)) released.tree.locations := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,protectedEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedInactiveWritableSharedRun.prepare input protections selected head tail writable raw
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedInactiveWritableSharedData.build input protections selected head tail writable raw
  have fits : input.tree.nodes.data.size≤4294967296 := by have a:=input.aligned;have b:=input.fits;omega
  have vacant : input.tree.nodes.get (index input)=none := by
    unfold UniValMap.get
    have endIndex : (index input).toNat=input.tree.nodes.data.size := GeneralBorrowFreshMetadataChildShared.at_end input
    rw [endIndex]
    simp
  have preserved := GeneralBorrowExposedScopedInactiveWritableCleanReadRange.ranged input.tree protections input.parentTag input.parent selected head (index input) tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) context raw.component.support writable fits input.parentTagPresent vacant clean
    input.well input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  have preparedClean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index prepared)=none) prepared.tree.locations := by
    rw [indexEq,treeEq]
    exact preserved.2
  have released := construct_release prepared protections selected head tail writable preparedRaw
    (by rw [offsetEq,lenEq];exact positive) preparedClean
  have frame := GeneralBorrowFreshReadFrame.frame input.tree (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed
  have childEq : result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections .VisitChildrenOfAccessed).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen input.isProtected).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,protectedEq,offsetEq,lenEq]
  rw [childEq,newTagEq] at released
  simpa only [indexEq,supportEq] using released

theorem run (input : Input) (global : GlobalState) (allocation : AllocId) (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool) (raw : Resources input global.protectedTags selected head tail writable)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input)=none) input.tree.locations)
    (initialTags : GeneralBorrowGcAllocator.NodeTags input.tree) :
    let released:=((GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child input global.protectedTags .VisitChildrenOfAccessed).releaseProtector input.newTag global.protectedTags).tree
    let ended:=(global.endCall (({} : FrameState).addProtector allocation input.newTag)).protectedTags
    GeneralRangeMapState.Every (fun location=>GeneralBorrowExposureCardinality.LocationCoherent released location ended ∧
      GeneralBorrowSifaWritableFrame.Profile released ended area.support location ∧
      GeneralBorrowExposedInactiveConstructor.Profile released location (index input) (fun position=>raw.component.support position∨position=(index input).toNat)) released.locations := by
  let released:=((GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child input global.protectedTags .VisitChildrenOfAccessed).releaseProtector input.newTag global.protectedTags).tree
  have globals:=held input global.protectedTags selected head tail writable raw positive clean
  have metadata:=GeneralBorrowExposedScopedInactiveWritableSharedMetadata.run input global.protectedTags selected head tail writable raw initialTags
  obtain ⟨helperNode,helperPresent,helperTag,helperHidden⟩:=metadata.2.2.2.1
  have hidden : ∀ query node,released.nodeAt query=some node→node.tag=input.newTag→node.isExposed=false := by
    intro query node present tag
    have lookup:=metadata.2.1 query node present
    change released.indexOfTag node.tag=some query at lookup
    have helperLookup : released.indexOfTag input.newTag=some (index input):=metadata.2.2.1
    rw [tag,helperLookup] at lookup
    have eq : query=index input:=(Option.some.inj lookup).symm
    subst query
    have same:=Option.some.inj (present.symm.trans helperPresent)
    subst node
    exact helperHidden
  dsimp only
  intro position valid
  have before:=globals position valid
  simp only [GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  refine ⟨GeneralBorrowProtectorCacheMap.remove_hidden released _ global.protectedTags input.newTag before.1 hidden,?_,before.2.2⟩
  intro query node included present
  obtain ⟨old,oldPresent,leaf,exposed⟩:=raw.leaves query included
  have different : node.tag≠input.newTag := by
    intro same
    have flag:=hidden query node present same
    obtain ⟨next,found,tag,flagEq⟩:=metadata.2.2.2.2 query old oldPresent
    have eq:=Option.some.inj (present.symm.trans found)
    subst node
    rw [flagEq,exposed] at flag
    cases flag
  unfold ProtectedTags.contains
  rw [GeneralBorrowProtectorCacheMap.remove_other global.protectedTags input.newTag node.tag different]
  exact before.2.1 query node included present
/-- Both profile modes retain whole-allocation cache coherence and old leaf
Write rights through the actual Read/child/release/endCall. Selected exposed
permissions are consumed only on the borrowed window; this deliberately does
not recover a global selected profile from window data. Legacy run is intact. -/
theorem run_pair {profileMode : ProfileMode} (input : Input) (global : GlobalState) (allocation : AllocId)
    (selected head : UniIndex) (tail : List UniIndex) (writable : Nat → Bool)
    (raw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input global.protectedTags selected head tail writable profileMode)
    (positive : input.offset.toNat < (input.offset+input.len).toNat)
    (clean : GeneralRangeMapState.Every (fun location : LocationTree => location.perms.get (index input)=none) input.tree.locations)
    (initialTags : GeneralBorrowGcAllocator.NodeTags input.tree) :
    let released := ((GeneralBorrowExposedScopedInactiveWritableSharedPathMetadata.child input global.protectedTags .VisitChildrenOfAccessed).releaseProtector input.newTag global.protectedTags).tree
    let ended := (global.endCall (({} : FrameState).addProtector allocation input.newTag)).protectedTags
    GeneralRangeMapState.Every (fun location => GeneralBorrowExposureCardinality.LocationCoherent released location ended ∧
      GeneralBorrowSifaWritableFrame.Profile released ended area.support location) released.locations :=
  GeneralBorrowExposedScopedInactiveWindowWritableSharedGlobal.run input global allocation selected head tail writable
    (GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor.toWindow input global.protectedTags selected head tail writable raw)
    positive clean initialTags

end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedGlobal
