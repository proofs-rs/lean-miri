import duplicate_prefix.CurrentCallSpatialSourceInstall
import duplicate_prefix.CurrentCallEmptyMissFacts
import duplicate_prefix.CurrentCallSelectedBoolWindow
import duplicate_prefix.CurrentCallEmptyEntryReturnWindow
namespace DuplicatePrefix.CurrentCallEmptyMissCurrent
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CurrentCallEmptyTypedEntry GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
private theorem firstFresh (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615) :
    tracker.global.nextPointerTag.value<18446744073709551615 :=
  UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (enabled : before.borrowTracker=some tracker)
    (frames : Array CompilerFrameContext.ActualFrame) (stackReady : CurrentCallPush.StackReadiness before frames)
    (address count : UInt64) (nonzero : address≠0)
    (addressMode : before.user.addresses.provenanceMode≠.strict)
    (miss : before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow before tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat)
    (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types) :

    let root:=CurrentCallSpatialEntryControl.root before frames place model.noDataRace
    ∃ (output : GeneralBorrowForestFnEntry.Output) (child : UniIndex) (machine : Before),
    ∃ nextData nextOwner,∃ Q : UniformWindow machine ⟨output.global,tracker.retagMode⟩ nextData nextOwner physical.id physical.offset.toNat 1 .ret,
    ∃ window : CurrentCallBoolScalarWrite.Window machine place,
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base (.pointer (Pointer.new .wildcard (Size.ofBytes address))) 0),.Copy (second count)]
        false (.memory place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState)=
        .ok () (Storage.withCurrent frames (CurrentCallEmptyMissFacts.frame options remaining span
          (CurrentCallPush.preparedMachine before frames) tracker root address count physical.id output.tag miss) machine) ∧
      DuplicatePrefixCallModel.Model options remaining span machine ∧
      machine.threads=(CurrentCallPush.preparedMachine before frames).threads ∧
      machine.borrowTracker=some ⟨output.global,tracker.retagMode⟩ ∧
      window.pointer=physical.pointer ∧ window.id=physical.id ∧ window.offset=physical.offset ∧
      window.entry.allocation=Q.allocation ∧
      CandidateCallBindings.WindowBinding machine window.pointer window.id window.offset.toNat 1 ∧
      CurrentCallBoolProtection.WindowReady machine window.id window.offset.toNat 1 ∧
      Q.pointer.grant=child ∧Q.pointer.value={B.pointer.value with provenance:=.concrete physical.id output.tag} ∧
      DuplicatePrefixBorrowContract.RuntimeFacts Q.allocation.extra output.global ∧
      Q.allocation.extra.roots.toList.Nodup ∧Q.allocation.extra.nodes.size<65536 ∧
      ∃ node,Q.allocation.extra.nodes.get child=some node ∧ node.tag=output.tag ∧ node.children=#[] ∧node.isExposed=false ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra child .Write physical.offset (physical.offset+1) ∧
      Q.precise.completion.parents[child.toNat]?=some (some B.pointer.grant) ∧
      SpatialDelegation machine ⟨output.global,tracker.retagMode⟩ physical.id Q.allocation Q.precise.completion B.pointer.grant ∧
      PointerBinds Q.allocation B.pointer ∧
      CurrentCallEmptyNoSourceFacts.Checkpoint before frames tracker machine output.global output.tag ∧
      machine.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup machine.memory)=.ok none := by
  dsimp only
  let fresh:=firstFresh tracker tagRoom
  let source:=CurrentCallEmptyMissEntry.sourceMachine options remaining span before tracker frames place model.noDataRace address miss fresh
  let next:={tracker with global:=advanced tracker.global fresh}
  let args:=CurrentCallEmptyMissEntry.argsRoot options remaining span before tracker frames place model.noDataRace address count miss
  obtain ⟨P,output,child,pointerP,allocationP,preciseP,actual,tag,rootTag,⟨witness⟩,updated,machine,
    entered,memory,tracked,user,threads,race,live,extra,bytes,length,borrow,returnPlace,maskWF,maskLen,mutable,mutation,snapshot,sourceUser,lookupEq,queryMiss,counter,flags,rootTags,trackedTags⟩ :=
    CurrentCallEmptyMissEntry.invoke options limits remaining span before tracker model enabled frames stackReady address count nonzero addressMode miss place physical
      data owner B pointer allocation runtime binding distinct tagRoom nodeRoom ready dynamicFuel validationFuel dynamicEq validationEq origins
  obtain ⟨P2,_,allocationP2,_,runtimeP2⟩ := CurrentCallEmptyUnlocatedCopy.advance B runtime fresh source rfl
  have runtimeP : DuplicatePrefixBorrowContract.RuntimeFacts P.allocation.extra next.global := by
    rw [allocationP,←allocationP2]
    exact runtimeP2
  have freshAfter : next.global.nextPointerTag.value<18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change (TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh).value.toNat<18446744073709551615
    rw [GenericFunctionEntryNumerics.successor_value]
    exact tagRoom
  let constructor:=borrowedState frames (atSpan args ⟨601⟩).frame {} source next freshAfter physical.id physical.entry output.child.tree
  have constructorPresent : Present (ActualWorld constructor.machine) physical.id (P.allocation.setExtra output.child.tree) := by
    simp only [Present,ActualWorld,Array.toList_map]
    apply List.mem_map.mpr
    refine ⟨(physical.id,{physical.entry with allocation:=physical.entry.allocation.setExtra output.child.tree}),?_,?_⟩
    · exact Array.mem_toList_iff.mpr (Array.mem_push.mpr (.inr rfl))
    · simp only [allocation,allocationP]
  have present : Present (ActualWorld machine) physical.id updated := by
    simp only [Present,ActualWorld,Array.toList_map]
    exact List.mem_map.mpr ⟨(physical.id,{physical.entry with allocation:=updated}),Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some live),rfl⟩
  have rootTagP : output.global.rootTag? physical.id=next.global.rootTag? physical.id:=rootTag
  have extra' : updated.extra=(output.child.tree.performBorrowAccessRange (.concrete output.tag) (Size.ofBytes physical.offset) (Size.ofBytes 1)
      .Write output.global.protectedTags .VisitChildrenOfAccessed).tree := by rw [tag];exact extra
  obtain ⟨nextData,nextOwner,Q,pointerQ,allocationQ,completionQ,runtimeQ,ownedQ,leaf,hidden,nodeAt,active,parentIssued,parentBinding⟩ :=
    CurrentCallSelectedBoolWindow.window P runtimeP {} freshAfter (by rw [allocationP];exact distinct) (by rw [allocationP];exact nodeRoom)
      physical.offset rfl output child actual witness tag constructor.machine constructorPresent rootTagP machine updated present
      (length.trans (congrArg Allocation.len (allocation.trans allocationP.symm)))
      (bytes.trans (congrArg Allocation.byteSize (allocation.trans allocationP.symm))) extra'
  have outputLiteral : output=CurrentCallTypedFnEntry.literal P.allocation.extra next.global {} physical.id freshAfter P.pointer.value.provenance physical.offset 1 :=
    Except.ok.inj (actual.symm.trans (CurrentCallTypedFnEntry.literal_operation _ _ _ _ freshAfter _ _ _))
  have outputGlobal : output.global=(registered next.global {} physical.id freshAfter).1 := by rw [outputLiteral];rfl
  have preparedModel := CurrentCallResourcePreparedEntry.model model frames
  have addresses : machine.user.addresses=before.user.addresses := by rw [user];rfl
  have extras : machine.user.payload.payload.user.runtime.extras=before.user.payload.payload.user.runtime.extras := by rw [user];rfl
  have modelAfter : DuplicatePrefixCallModel.Model options remaining span machine := by
    obtain ⟨old,oldEnabled,mode⟩:=model.defaultTracker
    have equal : old=tracker:=Option.some.inj (oldEnabled.symm.trans enabled)
    subst old
    refine ⟨model.debugOff,model.preciseOff,model.implicitOff,?_,?_,⟨⟨output.global,tracker.retagMode⟩,tracked,mode⟩,?_,?_,?_,?_,?_,?_,model.nullComparator,model.sourceMatches⟩
    · rw [user];exact preparedModel.ghostOff
    · rw [user];exact preparedModel.shallow
    · rw [race];exact model.noDataRace
    · rw [user];exact preparedModel.noBackend
    · rw [user];exact preparedModel.metadata
    · rw [threads];exact preparedModel.fixedScheduler
    · rw [user];exact preparedModel.unchecked
    · rw [user];exact preparedModel.noGc
  have singleMemory : machine.memory.live=(before.memory.live.filter (fun row=>row.1!=physical.id)).push (physical.id,{physical.entry with allocation:=updated}) := by
    exact memory.trans (congrArg MemoryState.live (MemoryCopyBridge.live_update_twice before.memory physical.id
      {physical.entry with allocation:=physical.entry.allocation.setExtra output.child.tree} {physical.entry with allocation:=updated}))
  have finalBinding : CandidateCallBindings.WindowBinding machine physical.pointer physical.id physical.offset.toNat 1 :=
    CurrentCallBoolWindow.replace_binding before machine physical.pointer physical.id physical.offset.toNat 1 binding physical.id physical.entry
      {physical.entry with allocation:=updated} physical.live length bytes addresses singleMemory
  have mutation' : Allocation.writeUninit (allocRange (Size.ofBytes physical.offset) (Size.ofBytes 1)) (Size.ofBytes 8)
      (physical.entry.allocation.setExtra updated.extra)=.ok () updated := by simpa only [Allocation.setExtra,Allocation.mapExtra] using mutation
  have updatedSelf : updated.setExtra updated.extra=updated:=by cases updated;rfl
  obtain ⟨window,windowPointer,windowId,windowOffset,windowEntry,windowBinding,windowReady⟩ := CurrentCallEmptyEntryReturnWindow.of_mutation physical updated.extra updated.extra updated mutation'
    (by rw [updatedSelf];exact live) addresses finalBinding ready extras
  have entered' := entered
  rw [←tag] at entered'
  have bounds : physical.offset.toNat+1≤P.allocation.extra.locations.size.bytes.toNat := by
    have bound := (P.window (physical.id,physical.offset.toNat) ⟨rfl,Nat.le_refl _,by omega⟩).1
    rw [P.issued.capability.treeExtent,←P.issued.capability.extent]
    omega
  have rootsAfter := (spatial_install_rule ".CurrentCallSelectedBoolCurrent.roots") P runtimeP {} freshAfter rfl
    (by rw [allocationP];exact distinct) (by rw [allocationP];omega) (by rw [allocationP];omega)
    physical.offset 1 rfl rfl (by decide) bounds output actual
  have growthAfter := (spatial_install_rule ".CurrentCallSelectedBoolCurrent.growth") P runtimeP {} freshAfter rfl
    (by rw [allocationP];exact distinct) (by rw [allocationP];omega) (by rw [allocationP];omega)
    physical.offset 1 rfl rfl (by decide) bounds output actual
  obtain ⟨_,_,_,_,writeNodes,writeRoots,_,_⟩ := CurrentCallSelectedBoolCurrent.operation_runtime P runtimeP {} freshAfter
    (by rw [allocationP];exact distinct) (by rw [allocationP];exact nodeRoom) physical.offset rfl output child actual witness tag
    constructor.machine constructorPresent rootTagP .VisitChildrenOfAccessed
  have rootsQ : Q.allocation.extra.roots.toList.Nodup := by rw [allocationQ,extra',writeRoots];exact rootsAfter
  have shortQ : Q.allocation.extra.nodes.size<65536 := by
    rw [allocationQ,extra',writeNodes]
    rw [allocationP] at growthAfter
    omega
  refine ⟨output,child,machine,nextData,nextOwner,Q,window,entered',modelAfter,threads,tracked,windowPointer,windowId,windowOffset,?_,windowBinding,windowReady,?_,?_,?_,rootsQ,?_,witness.node,?_,witness.tag,leaf,hidden,?_,?_,?_,?_,⟨sourceUser,lookupEq,counter,flags,rootTags,trackedTags⟩,queryMiss⟩
  · rw [windowEntry,updatedSelf,allocationQ]
  · rw [pointerQ];rfl
  · rw [pointerQ]
    change (⟨P.pointer.value.offset,Provenance.concrete physical.id output.tag⟩ : Pointer Provenance)=_
    rw [pointerP]
  · rw [allocationQ];exact runtimeQ
  · exact shortQ
  · rw [allocationQ];exact nodeAt
  · rw [allocationQ];exact active
  · rw [completionQ]
    change (S05ConcreteProtectedChildCompletion.extend P.precise.completion child P.pointer.grant).parents[child.toNat]?=_
    rw [pointerP]
    exact S05ConcreteProtectedChildCompletion.child_edge _ _ _
  · rw [allocationQ]
    rw [pointerP] at parentIssued
    exact parentIssued
  · rw [allocationQ]
    rw [pointerP] at parentBinding
    exact parentBinding
end
end DuplicatePrefix.CurrentCallEmptyMissCurrent
