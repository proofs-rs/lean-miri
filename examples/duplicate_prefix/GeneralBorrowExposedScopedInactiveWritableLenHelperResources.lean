import duplicate_prefix.GeneralBorrowExposedScopedSharedPathMetadata
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedNext
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedProtect
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedVacantClean
import duplicate_prefix.GeneralBorrowExposedScopedSharedMetadata
import duplicate_prefix.GeneralBorrowStructuralHistoryFrames
import duplicate_prefix.GeneralBorrowFreshSharedGeometry
import duplicate_prefix.GenericFunctionEntryNumerics
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableLenHelperResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open GeneralBorrowFreshMetadataChildShared GeneralBorrowExposedScopedInactiveWritableSharedConstructor
open GeneralBorrowExposedKnownRootState (Scope)
open GeneralBorrowStructuralHistoryState (State)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section
/-- The actual source shared-expression pipeline forms all registered-table
resources for the subsequent real len helper. Graph/tag accounting, clean
helper slot and expression-tag absence are derived from initial data. -/
theorem build (first : Input) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (tagEq : first.newTag=tracker.global.nextPointerTag)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources first tracker.global.protectedTags selected head tail (fun _=>true))
    (initial : State first.tree) (clean : GeneralBorrowGcVacantClean.VacantClean first.tree)
    (positive : first.offset.toNat<(first.offset+first.len).toNat)
    (futureFresh : GeneralBorrowTagMap.Fresh first.tree.tagMapping (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (room : first.tree.nodes.size+2<65536)
    (exprUnheld : tracker.global.protectedTags.contains first.newTag=false) :
    let next := ReferenceBorrowDriver.allocatedTracker tracker fresh
    let child := GeneralBorrowExposedScopedSharedPathMetadata.child first tracker.global.protectedTags .VisitChildrenOfAccessed
    ∃ helper : Input, helper.tree=child ∧ helper.parentTag=first.newTag ∧ helper.newTag=next.global.nextPointerTag ∧
      helper.parent=index first ∧ helper.isProtected=true ∧ helper.offset=first.offset ∧ helper.len=first.len ∧
      helper.offset.toNat<(helper.offset+helper.len).toNat ∧
      GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index helper)=none) helper.tree.locations ∧
      helper.tree.locations.size=first.tree.locations.size ∧
      helper.parentNode.tag=first.newTag ∧
      (TypedBorrowSteps.registeredGlobal next next.global.nextPointerTag).protectedTags.contains helper.parentNode.tag=false ∧
      ∃ registered : Resources helper (TypedBorrowSteps.registeredGlobal next next.global.nextPointerTag).protectedTags selected head tail
        (GeneralBorrowFreshMixedChild.extend (fun _=>true) (index first).toNat),
        GeneralBorrowGcAllocator.NodeTags helper.tree := by
  dsimp only
  let next := ReferenceBorrowDriver.allocatedTracker tracker fresh
  have numerical := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
  have different : first.newTag≠next.global.nextPointerTag := by
    rw [tagEq]
    intro same
    have equal := congrArg (fun tag : BorTag=>tag.value.toNat) same
    change next.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+1 at numerical
    omega
  obtain ⟨readDone,helper,helperTree,helperParentTag,helperNewTag,helperParent,helperProtected,helperOffset,helperLen,helperRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedInactiveWritableSharedNext.next first tracker.global.protectedTags selected head tail (fun _=>true) raw positive
      next.global.nextPointerTag futureFresh different room true
  obtain ⟨_,prepared,preparedTree,preparedParentTag,preparedNewTag,preparedParent,preparedProtected,preparedOffset,preparedLen,preparedIndex,preparedRaw,_⟩ :=
    GeneralBorrowExposedScopedInactiveWritableSharedRun.prepare first tracker.global.protectedTags selected head tail (fun _=>true) raw
  have readState := GeneralBorrowStructuralHistoryFrames.access first.tree initial (.concrete first.parentTag)
    (Size.ofBytes first.offset) (Size.ofBytes first.len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed first.bounds
  have preparedState : State prepared.tree := by rw [preparedTree];exact readState.1
  have preparedSize : prepared.tree.locations.size=first.tree.locations.size := by rw [preparedTree];exact readState.2
  have childEq : result prepared=GeneralBorrowExposedScopedSharedPathMetadata.child first tracker.global.protectedTags .VisitChildrenOfAccessed := by
    simp only [result,GeneralBorrowExposedScopedSharedPathMetadata.child,preparedTree,preparedParentTag,preparedNewTag,preparedProtected,preparedOffset,preparedLen]
  have helperEq : helper.tree=result prepared := helperTree.trans childEq.symm
  have helperTags : GeneralBorrowGcAllocator.NodeTags helper.tree := by
    rw [helperEq]
    exact GeneralBorrowExposedScopedSharedMetadata.construct_nodeTags prepared preparedState.allocator.nodeTags
  have helperSize : helper.tree.locations.size=first.tree.locations.size := by
    rw [helperEq]
    exact (GeneralBorrowFreshSharedGeometry.append_frame prepared).2.trans preparedSize
  have vacantClean : GeneralBorrowGcVacantClean.VacantClean helper.tree := by
    rw [helperTree]
    exact GeneralBorrowExposedScopedInactiveWritableSharedVacantClean.run first tracker.global.protectedTags selected head tail (fun _=>true) raw clean
  have helperClean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index helper)=none) helper.tree.locations := by
    apply vacantClean
    simp [UniValMap.get,at_end helper]
  have freshAbsent : helper.tree.indexOfTag next.global.nextPointerTag=none := by
    have fresh := helper.fresh
    rw [helperNewTag] at fresh
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find helper.tree.tagMapping _ fresh,Option.map_none]
  obtain ⟨registered,sameSupport⟩ := GeneralBorrowExposedScopedInactiveWritableSharedProtect.protect helper tracker.global.protectedTags next.global.nextPointerTag
    selected head tail _ helperRaw (by
      intro query node present same
      have mapped := helperTags query node present
      change helper.tree.indexOfTag node.tag=some query at mapped
      rw [same,freshAbsent] at mapped
      cases mapped)
  have parentNodeTag : helper.parentNode.tag=first.newTag := by
    obtain ⟨node,present,tag,_,_,_,_⟩ := (append prepared).newNode
    have presentHelper : helper.tree.nodeAt (index first)=some node := by
      rw [helperEq,←preparedIndex]
      exact present
    have same : helper.parentNode=node := Option.some.inj (helper.parentPresent.symm.trans (by rw [helperParent];exact presentHelper))
    rw [same,tag,preparedNewTag]
  have unheld : (TypedBorrowSteps.registeredGlobal next next.global.nextPointerTag).protectedTags.contains helper.parentNode.tag=false := by
    rw [parentNodeTag]
    change (tracker.global.protectedTags.insert next.global.nextPointerTag .StrongProtector).contains first.newTag=false
    rw [ProtectorInsertion.contains_other _ _ _ _ different]
    exact exprUnheld
  refine ⟨helper,helperTree,helperParentTag,helperNewTag,helperParent,helperProtected,helperOffset,helperLen,?_,helperClean,helperSize,parentNodeTag,unheld,registered,helperTags⟩
  · rw [helperOffset,helperLen]
    exact positive

/-- Actual shared-expression execution forms registered len-helper resources
with the same explicit proof scope. Window mode never yields a global profile. -/
theorem build_mode {profileMode : ProfileMode} (first : Input) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value<18446744073709551615)
    (tagEq : first.newTag=tracker.global.nextPointerTag)
    (selected head : UniIndex) (tail : List UniIndex)
    (raw : ResourcesFor first tracker.global.protectedTags selected head tail (fun _=>true) profileMode)
    (initial : State first.tree) (clean : GeneralBorrowGcVacantClean.VacantClean first.tree)
    (positive : first.offset.toNat<(first.offset+first.len).toNat)
    (futureFresh : GeneralBorrowTagMap.Fresh first.tree.tagMapping (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
    (room : first.tree.nodes.size+2<65536)
    (exprUnheld : tracker.global.protectedTags.contains first.newTag=false) :
    let next := ReferenceBorrowDriver.allocatedTracker tracker fresh
    let child := GeneralBorrowExposedScopedSharedPathMetadata.child first tracker.global.protectedTags .VisitChildrenOfAccessed
    ∃ helper : Input, helper.tree=child ∧ helper.parentTag=first.newTag ∧ helper.newTag=next.global.nextPointerTag ∧
      helper.parent=index first ∧ helper.isProtected=true ∧ helper.offset=first.offset ∧ helper.len=first.len ∧
      helper.offset.toNat<(helper.offset+helper.len).toNat ∧
      GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index helper)=none) helper.tree.locations ∧
      helper.tree.locations.size=first.tree.locations.size ∧
      helper.parentNode.tag=first.newTag ∧
      (TypedBorrowSteps.registeredGlobal next next.global.nextPointerTag).protectedTags.contains helper.parentNode.tag=false ∧
      ∃ registered : ResourcesFor helper (TypedBorrowSteps.registeredGlobal next next.global.nextPointerTag).protectedTags selected head tail
        (GeneralBorrowFreshMixedChild.extend (fun _=>true) (index first).toNat) profileMode,
        GeneralBorrowGcAllocator.NodeTags helper.tree := by
  dsimp only
  let next := ReferenceBorrowDriver.allocatedTracker tracker fresh
  have numerical := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag fresh
  have different : first.newTag≠next.global.nextPointerTag := by
    rw [tagEq]
    intro same
    have equal := congrArg (fun tag : BorTag=>tag.value.toNat) same
    change next.global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+1 at numerical
    omega
  obtain ⟨readDone,helper,helperTree,helperParentTag,helperNewTag,helperParent,helperProtected,helperOffset,helperLen,helperRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedInactiveWritableSharedNext.next_mode first tracker.global.protectedTags selected head tail (fun _=>true) raw positive
      next.global.nextPointerTag futureFresh different room true
  obtain ⟨_,prepared,preparedTree,preparedParentTag,preparedNewTag,preparedParent,preparedProtected,preparedOffset,preparedLen,preparedIndex,preparedRaw,_⟩ :=
    GeneralBorrowExposedScopedInactiveWritableSharedRun.prepare_mode first tracker.global.protectedTags selected head tail (fun _=>true) raw
  have readState := GeneralBorrowStructuralHistoryFrames.access first.tree initial (.concrete first.parentTag)
    (Size.ofBytes first.offset) (Size.ofBytes first.len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed first.bounds
  have preparedState : State prepared.tree := by rw [preparedTree];exact readState.1
  have preparedSize : prepared.tree.locations.size=first.tree.locations.size := by rw [preparedTree];exact readState.2
  have childEq : result prepared=GeneralBorrowExposedScopedSharedPathMetadata.child first tracker.global.protectedTags .VisitChildrenOfAccessed := by
    simp only [result,GeneralBorrowExposedScopedSharedPathMetadata.child,preparedTree,preparedParentTag,preparedNewTag,preparedProtected,preparedOffset,preparedLen]
  have helperEq : helper.tree=result prepared := helperTree.trans childEq.symm
  have helperTags : GeneralBorrowGcAllocator.NodeTags helper.tree := by
    rw [helperEq]
    exact GeneralBorrowExposedScopedSharedMetadata.construct_nodeTags prepared preparedState.allocator.nodeTags
  have helperSize : helper.tree.locations.size=first.tree.locations.size := by
    rw [helperEq]
    exact (GeneralBorrowFreshSharedGeometry.append_frame prepared).2.trans preparedSize
  have vacantClean : GeneralBorrowGcVacantClean.VacantClean helper.tree := by
    rw [helperTree]
    exact GeneralBorrowExposedScopedInactiveWritableSharedVacantClean.run first tracker.global.protectedTags selected head tail (fun _=>true) raw clean
  have helperClean : GeneralRangeMapState.Every (fun location : LocationTree=>location.perms.get (index helper)=none) helper.tree.locations := by
    apply vacantClean
    simp [UniValMap.get,at_end helper]
  have freshAbsent : helper.tree.indexOfTag next.global.nextPointerTag=none := by
    have fresh := helper.fresh
    rw [helperNewTag] at fresh
    simp only [BorrowTree.indexOfTag,UniKeyMap.get,GeneralBorrowTagMap.fresh_find helper.tree.tagMapping _ fresh,Option.map_none]
  obtain ⟨registered,sameSupport⟩ := GeneralBorrowExposedScopedInactiveWritableSharedProtect.protect helper tracker.global.protectedTags next.global.nextPointerTag
    selected head tail _ helperRaw (by
      intro query node present same
      have mapped := helperTags query node present
      change helper.tree.indexOfTag node.tag=some query at mapped
      rw [same,freshAbsent] at mapped
      cases mapped)
  have parentNodeTag : helper.parentNode.tag=first.newTag := by
    obtain ⟨node,present,tag,_,_,_,_⟩ := (append prepared).newNode
    have presentHelper : helper.tree.nodeAt (index first)=some node := by
      rw [helperEq,←preparedIndex]
      exact present
    have same : helper.parentNode=node := Option.some.inj (helper.parentPresent.symm.trans (by rw [helperParent];exact presentHelper))
    rw [same,tag,preparedNewTag]
  have unheld : (TypedBorrowSteps.registeredGlobal next next.global.nextPointerTag).protectedTags.contains helper.parentNode.tag=false := by
    rw [parentNodeTag]
    change (tracker.global.protectedTags.insert next.global.nextPointerTag .StrongProtector).contains first.newTag=false
    rw [ProtectorInsertion.contains_other _ _ _ _ different]
    exact exprUnheld
  refine ⟨helper,helperTree,helperParentTag,helperNewTag,helperParent,helperProtected,helperOffset,helperLen,?_,helperClean,helperSize,parentNodeTag,unheld,registered,helperTags⟩
  · rw [helperOffset,helperLen]
    exact positive
end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableLenHelperResources
