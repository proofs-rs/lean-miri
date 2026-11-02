import duplicate_prefix.CurrentCallSpatialSourceState
import duplicate_prefix.PositiveGlobalTypedReborrow
import duplicate_prefix.CurrentCallSpatialEntryActivity
import duplicate_prefix.CurrentCallPostEntryCheckpoint

/-! The actual spatial source copy produces the current source interface used
by the common continuation, before Bool protection. Each retained proof cell
keeps the source constructor's fixed extension; no whole-source C is selected. -/
namespace DuplicatePrefix.CurrentCallSpatialSourceCheckpoint
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CurrentCallSpatialCover CurrentCallPostEntryCheckpoint
open CanonicalConfigFacts ActualReferenceContext TypedBorrowSteps ReferenceBorrowDriver
open CurrentCallSpatialSourceInstall CurrentCallTypedSourceCopy GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (before : Before) (tracker : MachineHooks.BorrowState) (cover : Context before)
    (offset : Nat) (len : UInt64) (role : RoleCover before tracker cover .mut offset len.toNat)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts role.backing.allocation.extra tracker.global)
    (state : DuplicatePrefixRuntimeInput.State before tracker)
    (highwater : ∀row∈before.memory.live.toList,GeneralBorrowForestTagHighWater.Below row.2.allocation.extra tracker.global.protectedTags tracker.global.nextPointerTag)
    (distinct : role.backing.allocation.extra.roots.toList.Nodup)
    (sourceRoom : role.backing.allocation.extra.nodes.size+7<65536)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker=some borrowFrame)
    (binding : CandidateCallBindings.WindowBinding before role.family.value role.backing.id offset len.toNat)
    (positive : 0<len.toNat) (signedFits : len.toNat<9223372036854775808)
    (room : tracker.global.nextPointerTag.value<18446744073709551615) (race : before.dataRace=none)
    (nullComparator : ProjectionMetadataFacts.NullComparator) (dynamicFuel validationFuel : Nat)
    (fuelEq : options.place.dynamicFuel=dynamicFuel+1) (validationEq : options.limits.validation=validationFuel+1)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)).metadata=PreparedReflection.actual.runtime)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame before)))
    (debugOff : options.place.debugAssertions=false) (ghostOff : before.user.payload.ghost=false)
    (shallowMode : before.user.payload.validation=.Shallow)
    (localId : MIR.LocalId) (valid : localId<frame.locals.size) (old : Immediate Provenance)
    (live : frame.locals[localId].value=.live (.immediate old))
    (cached : frame.locals[localId].layout=some ActualReferenceMetadata.reference) (noClocks : frame.extra.dataRace=none)
    (storage : CurrentCallResourceEntrySourceStorage.Data role.backing.allocation (UInt64.ofNat offset) len)
    (profile : CurrentCallBoolProtection.WindowReady before role.backing.id offset len.toNat) :
    let output:=CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len
    ∃(entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (doneFrame : CompilerFrameContext.ActualFrame),
      ∃source : Source (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry)
          ⟨output.global,tracker.retagMode⟩ offset len,
      CopyReady source ∧
      MachineHooks.withRetagMode .FnEntry
        ((ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
          ⟨.immediate (value options remaining span role.family.value len).imm,ActualReferenceMetadata.reference⟩
          (LocalPlaces.localRuntimePlace frames.size frame localId ActualReferenceMetadata.reference).stackView)
        (Storage.withCurrent frames frame before)=
        .ok () (Storage.withCurrent frames doneFrame (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry)) ∧
      before.memory.live.find? (fun row=>row.1==role.backing.id)=some (role.backing.id,entry) ∧entry.allocation=role.backing.allocation ∧
      source.role.family=childFamily role output.tag ∧source.tag=tracker.global.nextPointerTag ∧source.role.backing.allocation=role.backing.allocation.setExtra output.child.tree ∧
      doneFrame.extra.borrowTracker=some output.frame ∧
      DuplicatePrefixRuntimeInput.State (copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry) ⟨output.global,tracker.retagMode⟩ := by
  have short : role.backing.allocation.extra.nodes.size<65536:=by omega
  have nodeRoom : role.backing.allocation.extra.nodes.size+1≤4294967295:=by omega
  obtain ⟨entry,doneFrame,child,installed,oldLive,allocation,copy,lookup,borrowed,_,_,_,_,_,_,postState,postHighwater,current,view,familyEq,backingEq⟩:=
    CurrentCallSpatialSourceState.invoke options limits remaining span ctx before tracker cover offset len role runtime state highwater
      distinct short nodeRoom frames frame borrowFrame frameBorrow binding positive signedFits room race nullComparator dynamicFuel validationFuel
      fuelEq validationEq metadata origins debugOff ghostOff shallowMode localId valid old live cached noClocks
  let output:=CurrentCallSpatialEntryRead.output role borrowFrame room (UInt64.ofNat offset) len
  let post:=copiedMachine role borrowFrame room (UInt64.ofNat offset) len entry
  have viewAllocation : view.backing.allocation=role.backing.allocation.setExtra output.child.tree:=by rw [backingEq];rfl
  have viewId : view.backing.id=role.backing.id:=by rw [backingEq];rfl
  have fit : offset<2^64 := by
    obtain ⟨entry,address,_,_,length,_,bound,_⟩:=binding
    rw [length] at bound
    have capacity:=entry.allocation.byteSize.bytes.toNat_lt
    omega
  have startEq : (UInt64.ofNat offset).toNat=offset:=by rw [UInt64.toNat_ofNat',Nat.mod_eq_of_lt fit]
  have bounds : (UInt64.ofNat offset).toNat+len.toNat≤role.backing.allocation.extra.locations.size.bytes.toNat := by
    rw [startEq,←allocation,state.treeLength (role.backing.id,entry) (Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some oldLive))]
    rw [allocation]
    simpa only [startEq] using storage.slice.bounds
  have nonzero : len≠0:=by intro zero;rw [zero] at positive;cases positive
  obtain ⟨afterRuntime,_,q,node,qLookup,nodeAt,nodeTag,leaf,hidden,active⟩:=
    (positive_global_rule ".CurrentCallSpatialEntryActivity.spatial_facets") role runtime borrowFrame room rfl distinct short nodeRoom
      (UInt64.ofNat offset) len startEq rfl nonzero bounds
  have childEq : q=child := Option.some.inj (qLookup.symm.trans lookup)
  subst q
  have viewBinding : CandidateCallBindings.WindowBinding post view.family.value view.backing.id offset len.toNat := by
    obtain ⟨physical,address,physicalLive,cachedAddress,physicalStorage,addressRoom,physicalBounds,pointerAddress,nonnull,provenance⟩:=binding
    have same : physical=entry := (Prod.mk.inj (Option.some.inj (physicalLive.symm.trans oldLive))).2
    subst physical
    rw [familyEq,viewId]
    refine ⟨{entry with allocation:=entry.allocation.setExtra output.child.tree},address,
      MemoryCopyBridge.live_lookup_replaced _ _ _,cachedAddress,physicalStorage,addressRoom,physicalBounds,pointerAddress,nonnull,?_⟩
    rfl
  obtain ⟨_,_,_,_,_,growth,_⟩:=CurrentCallSpatialEntryConstructor.invoke role rfl runtime distinct short nodeRoom borrowFrame room
    (UInt64.ofNat offset) len startEq rfl nonzero bounds
  have rootDistinct:=(positive_global_rule ".CurrentCallSpatialSourceState.roots") role rfl runtime distinct short nodeRoom borrowFrame room
    (UInt64.ofNat offset) len startEq rfl nonzero bounds
  let source : Source post ⟨output.global,tracker.retagMode⟩ offset len := {
    context:=CurrentCallSpatialSourceCover.context role current (updates role rfl installed),role:=view,
    runtime:=by rw [viewAllocation];exact afterRuntime,
    distinct:=by rw [viewAllocation];exact rootDistinct,
    tag:=tracker.global.nextPointerTag,concrete:=by rw [familyEq,viewId];rfl,
    grant:=child,node:=node,nodeAt:=by rw [viewAllocation];exact nodeAt,
    nodeTag:=nodeTag,hidden:=hidden,activity:=by rw [viewAllocation];exact active,
    binding:=viewBinding,positive:=positive,signedFits:=signedFits,nodes:=by
      rw [viewAllocation]
      change output.child.tree.nodes.size+6<65536
      change output.child.tree.nodes.size≤role.backing.allocation.extra.nodes.size+1 at growth
      omega}
  have sourceReady : CopyReady source := by
    refine ⟨?_,?_⟩
    · change CurrentCallResourceEntrySourceStorage.Data view.backing.allocation (UInt64.ofNat offset) len
      rw [viewAllocation];exact storage.set_extra _
    · change CurrentCallBoolProtection.WindowReady post view.backing.id offset len.toNat
      rw [viewId];exact profile
  exact ⟨entry,doneFrame,source,sourceReady,copy,oldLive,allocation,familyEq,rfl,viewAllocation,borrowed,postState⟩

end
end DuplicatePrefix.CurrentCallSpatialSourceCheckpoint
