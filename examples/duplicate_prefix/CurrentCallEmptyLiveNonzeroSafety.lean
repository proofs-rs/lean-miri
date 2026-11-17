import duplicate_prefix.CurrentCallEmptyLiveSourceFacts
import duplicate_prefix.CurrentCallEmptyLiveSameNonzeroFinish
import duplicate_prefix.CurrentCallEmptyLiveDifferentNonzeroFinish
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.PushThread
namespace DuplicatePrefix.CurrentCallEmptyLiveNonzeroSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
theorem concrete_same (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (initial : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span initial)
    (enabled : initial.borrowTracker=some tracker)
    (stackReady : CurrentCallPush.StackReadiness initial #[])
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow initial place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow initial tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding initial physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : physical.entry.allocation.extra.indexOfTag parentTag=some parent)
    (parentAt : physical.entry.allocation.extra.nodeAt parent=some parentNode)
    (start : UInt64) (nonzero : physical.base+start≠0)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+3<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+4<65536)
    (ready : CurrentCallBoolProtection.WindowReady initial physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins initial.user.payload.payload.user.types)
    (count : UInt64) (countNonzero : count≠0) (budget : Nat) (dispatchEq : limits.callDispatch=budget+1) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span initial (.pointer (Pointer.new (.concrete physical.id parentTag) (Size.ofBytes (physical.base+start)))) 0 count place := by
  obtain ⟨output,child,machine,frame,nextData,nextOwner,Q,entered,tracked,grantQ,concreteQ,older,runtimeQ,rootsQ,shortQ,
    parentIssued,parentBinding,edge,returnPlace,borrow,installed,sourceHidden,modelAfter,threads,
    ⟨window,windowPointer,windowId,windowOffset,windowAllocation,windowBinding,windowReady⟩,
    ⟨sourceEntry,sourceLive,sourceLeaf,facts⟩,node,nodeAt,nodeTag,leaf,hidden,activity⟩ :=
    CurrentCallEmptyLiveSourceFacts.Concrete.same options limits remaining span initial tracker model enabled #[] stackReady place physical data owner B pointer allocation runtime binding distinct parentTag parent parentNode tagged parentAt start count nonzero (by omega) (by omega) ready dynamicFuel validationFuel dynamicEq validationEq origins
  let root:=CurrentCallSpatialEntryControl.root initial #[] place model.noDataRace
  let adjusted : Immediate Provenance:=(DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base (.pointer (Pointer.new (.concrete physical.id tracker.global.nextPointerTag) (Size.ofBytes (physical.base+start)))) 0 ActualReferenceMetadata.reference).imm
  have installed' : frame=PositiveRootInstalledFrame.installed root adjusted count {} physical.id tracker.global.nextPointerTag physical.id node.tag := by
    rw [nodeTag]
    exact installed
  obtain ⟨oldThread,oldActive,_⟩:=stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have active : machine.threads.activeThread?=some thread := by
    rw [threads]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot initial).1 oldThread 0 oldActive
  have currentAt : Q.allocation.extra.nodes.get Q.pointer.grant=some node := by rw [grantQ];exact nodeAt
  have currentActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra Q.pointer.grant .Write window.offset (window.offset+1) := by
    rw [grantQ,windowOffset];exact activity
  have currentEdge : Q.precise.completion.parents[Q.pointer.grant.toNat]?=some (some B.pointer.grant) := by rw [grantQ];exact edge
  have sourceAlloc : sourceEntry.allocation=Q.allocation := by
    have sameEntry : sourceEntry=window.entry := (Prod.mk.inj (Option.some.inj (sourceLive.symm.trans (by rw [←windowId];exact window.live)))).2
    exact (congrArg LocalAllocation.allocation sameEntry).trans windowAllocation
  rw [sourceAlloc] at sourceLeaf
  obtain ⟨qi,qn,qt,qa,qtag,_,qh,qinactive⟩:=sourceLeaf
  have currentRoom : Q.allocation.extra.nodes.size+2<65536 := by have growth:=facts.boolGrowth;omega
  have helperRoom : output.global.nextPointerTag.value.toNat+1<18446744073709551615 := by rw [facts.counter];omega
  have oldQ : tracker.global.nextPointerTag.value.toNat<node.tag.value.toNat := by rw [nodeTag];exact UInt64.lt_iff_toNat_lt.mp older
  obtain ⟨final,trace,terminal,emptyStack⟩:=CurrentCallEmptyLiveSameNonzeroFinish.finish options limits remaining span place B Q window windowBinding windowId
    (congrArg UInt64.toNat windowOffset) (windowPointer.trans pointer) windowAllocation parentIssued parentBinding runtimeQ rootsQ currentRoom
    ⟨physical.id,output.tag,concreteQ⟩ node currentAt hidden currentActive tracker.global.nextPointerTag qi qn qt qa qtag qh
    (CurrentCallResourceEmptyRootRelease.quiescent_of_inactive _ _ _ qinactive) oldQ physical.base start count nonzero countNonzero facts.cached
    root (RootEntryFrame.raw_locals _ _ _) frame installed' rfl rfl rfl modelAfter facts.origins tracked thread active rfl currentEdge windowReady helperRoom
    dynamicFuel validationFuel budget dynamicEq validationEq dispatchEq
  let start:=Storage.withCurrent #[] frame machine
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨config options (remaining+1) span,limits,fun _ _=>True⟩
  have callEntry : CallSafety.IsCallEntry 1 start:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [emptyStack];decide
  exact ⟨start,final,entered,trace,terminal,emptyStack,
    SuccessfulTrace.no_errors context 1 start final callEntry trace past,
    SuccessfulTrace.no_ub context 1 start final callEntry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

theorem concrete_different (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (initial : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span initial)
    (enabled : initial.borrowTracker=some tracker)
    (stackReady : CurrentCallPush.StackReadiness initial #[])
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow initial place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow initial tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding initial physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (sourceId : AllocId) (different : sourceId≠physical.id)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : initial.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,entry))
    (sourceBase : UInt64)
    (sourceCached : initial.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,sourceBase⟩)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (sourceRoom : entry.allocation.extra.nodes.size+3≤4294967295)
    (parentTag : BorTag) (parent : UniIndex) (parentNode : TreeNode)
    (tagged : entry.allocation.extra.indexOfTag parentTag=some parent)
    (parentAt : entry.allocation.extra.nodeAt parent=some parentNode)
    (start : UInt64) (nonzero : sourceBase+start≠0)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+3<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady initial physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins initial.user.payload.payload.user.types)
    (count : UInt64) (countNonzero : count≠0) (budget : Nat) (dispatchEq : limits.callDispatch=budget+1) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span initial (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes (sourceBase+start)))) 0 count place := by
  obtain ⟨output,child,machine,frame,nextData,nextOwner,Q,entered,tracked,grantQ,concreteQ,older,runtimeQ,rootsQ,shortQ,
    parentIssued,parentBinding,edge,returnPlace,borrow,installed,sourceHidden,modelAfter,threads,
    ⟨window,windowPointer,windowId,windowOffset,windowAllocation,windowBinding,windowReady⟩,
    ⟨sourceEntry,sourceLive,sourceLeaf,facts⟩,node,nodeAt,nodeTag,leaf,hidden,activity⟩ :=
    CurrentCallEmptyLiveSourceFacts.Concrete.different options limits remaining span initial tracker model enabled #[] stackReady place physical data owner B pointer allocation runtime binding distinct sourceId different entry sourceLive sourceBase sourceCached sourceRuntime (by omega) parentTag parent parentNode tagged parentAt start count nonzero (by omega) (by omega) ready dynamicFuel validationFuel dynamicEq validationEq origins
  let root:=CurrentCallSpatialEntryControl.root initial #[] place model.noDataRace
  let adjusted : Immediate Provenance:=(DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base (.pointer (Pointer.new (.concrete sourceId tracker.global.nextPointerTag) (Size.ofBytes (sourceBase+start)))) 0 ActualReferenceMetadata.reference).imm
  have installed' : frame=PositiveRootInstalledFrame.installed root adjusted count {} sourceId tracker.global.nextPointerTag physical.id node.tag := by
    rw [nodeTag]
    exact installed
  obtain ⟨oldThread,oldActive,_⟩:=stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have active : machine.threads.activeThread?=some thread := by
    rw [threads]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot initial).1 oldThread 0 oldActive
  have currentAt : Q.allocation.extra.nodes.get Q.pointer.grant=some node := by rw [grantQ];exact nodeAt
  have currentActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra Q.pointer.grant .Write window.offset (window.offset+1) := by
    rw [grantQ,windowOffset];exact activity
  have currentEdge : Q.precise.completion.parents[Q.pointer.grant.toNat]?=some (some B.pointer.grant) := by rw [grantQ];exact edge
  obtain ⟨qi,qn,qt,qa,qtag,_,qh,qinactive⟩:=sourceLeaf
  have currentSourceRoom : sourceEntry.allocation.extra.nodes.size+2≤4294967295 := by have growth:=facts.sourceGrowth;omega
  have helperRoom : output.global.nextPointerTag.value.toNat+1<18446744073709551615 := by rw [facts.counter];omega
  obtain ⟨final,trace,terminal,emptyStack⟩:=CurrentCallEmptyLiveDifferentNonzeroFinish.finish options limits remaining span place B Q window windowBinding windowId
    (congrArg UInt64.toNat windowOffset) (windowPointer.trans pointer) windowAllocation parentIssued parentBinding runtimeQ rootsQ shortQ
    ⟨physical.id,output.tag,concreteQ⟩ node currentAt hidden currentActive sourceId sourceEntry sourceLive different facts.sourceRuntime currentSourceRoom
    tracker.global.nextPointerTag qi qn qt qa qh (CurrentCallResourceEmptyRootRelease.quiescent_of_inactive _ _ _ qinactive) sourceHidden
    sourceBase start count nonzero countNonzero facts.cached root (RootEntryFrame.raw_locals _ _ _) frame installed' rfl rfl rfl modelAfter facts.origins tracked thread active rfl
    currentEdge windowReady helperRoom dynamicFuel validationFuel budget dynamicEq validationEq dispatchEq
  let start:=Storage.withCurrent #[] frame machine
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨config options (remaining+1) span,limits,fun _ _=>True⟩
  have callEntry : CallSafety.IsCallEntry 1 start:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [emptyStack];decide
  exact ⟨start,final,entered,trace,terminal,emptyStack,
    SuccessfulTrace.no_errors context 1 start final callEntry trace past,
    SuccessfulTrace.no_ub context 1 start final callEntry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

theorem wildcard_same (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (initial : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span initial)
    (enabled : initial.borrowTracker=some tracker)
    (stackReady : CurrentCallPush.StackReadiness initial #[])
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow initial place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow initial tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding initial physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (start : UInt64) (nonzero : physical.base+start≠0)
    (addressMode : initial.user.addresses.provenanceMode≠.strict)
    (inverse : WildcardGeneralHitReborrow.Geometry initial.user.addresses.intToPtrMap (physical.base+start) physical.base physical.id physical.entry.allocation.byteSize)
    (exposed : initial.user.addresses.exposed.contains physical.id=true)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+3<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+4<65536)
    (ready : CurrentCallBoolProtection.WindowReady initial physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins initial.user.payload.payload.user.types)
    (count : UInt64) (countNonzero : count≠0) (budget : Nat) (dispatchEq : limits.callDispatch=budget+1) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span initial (.pointer (Pointer.new (.wildcard) (Size.ofBytes (physical.base+start)))) 0 count place := by
  obtain ⟨output,child,machine,frame,nextData,nextOwner,Q,entered,tracked,grantQ,concreteQ,older,runtimeQ,rootsQ,shortQ,
    parentIssued,parentBinding,edge,returnPlace,borrow,installed,sourceHidden,modelAfter,threads,
    ⟨window,windowPointer,windowId,windowOffset,windowAllocation,windowBinding,windowReady⟩,
    ⟨sourceEntry,sourceLive,sourceLeaf,facts⟩,node,nodeAt,nodeTag,leaf,hidden,activity⟩ :=
    CurrentCallEmptyLiveSourceFacts.Wildcard.same options limits remaining span initial tracker model enabled #[] stackReady place physical data owner B pointer allocation runtime binding distinct start count nonzero addressMode inverse exposed (by omega) (by omega) ready dynamicFuel validationFuel dynamicEq validationEq origins
  let root:=CurrentCallSpatialEntryControl.root initial #[] place model.noDataRace
  let adjusted : Immediate Provenance:=(DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base (.pointer (Pointer.new (.concrete physical.id tracker.global.nextPointerTag) (Size.ofBytes (physical.base+start)))) 0 ActualReferenceMetadata.reference).imm
  have installed' : frame=PositiveRootInstalledFrame.installed root adjusted count {} physical.id tracker.global.nextPointerTag physical.id node.tag := by
    rw [nodeTag]
    exact installed
  obtain ⟨oldThread,oldActive,_⟩:=stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have active : machine.threads.activeThread?=some thread := by
    rw [threads]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot initial).1 oldThread 0 oldActive
  have currentAt : Q.allocation.extra.nodes.get Q.pointer.grant=some node := by rw [grantQ];exact nodeAt
  have currentActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra Q.pointer.grant .Write window.offset (window.offset+1) := by
    rw [grantQ,windowOffset];exact activity
  have currentEdge : Q.precise.completion.parents[Q.pointer.grant.toNat]?=some (some B.pointer.grant) := by rw [grantQ];exact edge
  have sourceAlloc : sourceEntry.allocation=Q.allocation := by
    have sameEntry : sourceEntry=window.entry := (Prod.mk.inj (Option.some.inj (sourceLive.symm.trans (by rw [←windowId];exact window.live)))).2
    exact (congrArg LocalAllocation.allocation sameEntry).trans windowAllocation
  rw [sourceAlloc] at sourceLeaf
  obtain ⟨qi,qn,qt,qa,qtag,_,qh,qinactive⟩:=sourceLeaf
  have currentRoom : Q.allocation.extra.nodes.size+2<65536 := by have growth:=facts.boolGrowth;omega
  have helperRoom : output.global.nextPointerTag.value.toNat+1<18446744073709551615 := by rw [facts.counter];omega
  have oldQ : tracker.global.nextPointerTag.value.toNat<node.tag.value.toNat := by rw [nodeTag];exact UInt64.lt_iff_toNat_lt.mp older
  obtain ⟨final,trace,terminal,emptyStack⟩:=CurrentCallEmptyLiveSameNonzeroFinish.finish options limits remaining span place B Q window windowBinding windowId
    (congrArg UInt64.toNat windowOffset) (windowPointer.trans pointer) windowAllocation parentIssued parentBinding runtimeQ rootsQ currentRoom
    ⟨physical.id,output.tag,concreteQ⟩ node currentAt hidden currentActive tracker.global.nextPointerTag qi qn qt qa qtag qh
    (CurrentCallResourceEmptyRootRelease.quiescent_of_inactive _ _ _ qinactive) oldQ physical.base start count nonzero countNonzero facts.cached
    root (RootEntryFrame.raw_locals _ _ _) frame installed' rfl rfl rfl modelAfter facts.origins tracked thread active rfl currentEdge windowReady helperRoom
    dynamicFuel validationFuel budget dynamicEq validationEq dispatchEq
  let start:=Storage.withCurrent #[] frame machine
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨config options (remaining+1) span,limits,fun _ _=>True⟩
  have callEntry : CallSafety.IsCallEntry 1 start:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [emptyStack];decide
  exact ⟨start,final,entered,trace,terminal,emptyStack,
    SuccessfulTrace.no_errors context 1 start final callEntry trace past,
    SuccessfulTrace.no_ub context 1 start final callEntry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

theorem wildcard_different (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (initial : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span initial)
    (enabled : initial.borrowTracker=some tracker)
    (stackReady : CurrentCallPush.StackReadiness initial #[])
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow initial place)
    (data : Identities) (owner : Nat)
    (B : UniformWindow initial tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding initial physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (sourceId : AllocId) (different : sourceId≠physical.id)
    (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (sourceLive : initial.memory.live.find? (fun row=>row.1==sourceId)=some (sourceId,entry))
    (sourceBase : UInt64)
    (sourceCached : initial.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,sourceBase⟩)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (sourceRoom : entry.allocation.extra.nodes.size+3≤4294967295)
    (start : UInt64) (nonzero : sourceBase+start≠0)
    (addressMode : initial.user.addresses.provenanceMode≠.strict)
    (inverse : WildcardGeneralHitReborrow.Geometry initial.user.addresses.intToPtrMap (sourceBase+start) sourceBase sourceId entry.allocation.byteSize)
    (exposed : initial.user.addresses.exposed.contains sourceId=true)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+3<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady initial physical.id physical.offset.toNat 1)
    (dynamicFuel validationFuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins initial.user.payload.payload.user.types)
    (count : UInt64) (countNonzero : count≠0) (budget : Nat) (dispatchEq : limits.callDispatch=budget+1) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span initial (.pointer (Pointer.new (.wildcard) (Size.ofBytes (sourceBase+start)))) 0 count place := by
  obtain ⟨output,child,machine,frame,nextData,nextOwner,Q,entered,tracked,grantQ,concreteQ,older,runtimeQ,rootsQ,shortQ,
    parentIssued,parentBinding,edge,returnPlace,borrow,installed,sourceHidden,modelAfter,threads,
    ⟨window,windowPointer,windowId,windowOffset,windowAllocation,windowBinding,windowReady⟩,
    ⟨sourceEntry,sourceLive,sourceLeaf,facts⟩,node,nodeAt,nodeTag,leaf,hidden,activity⟩ :=
    CurrentCallEmptyLiveSourceFacts.Wildcard.different options limits remaining span initial tracker model enabled #[] stackReady place physical data owner B pointer allocation runtime binding distinct sourceId different entry sourceLive sourceBase sourceCached sourceRuntime (by omega) start count nonzero addressMode inverse exposed (by omega) (by omega) ready dynamicFuel validationFuel dynamicEq validationEq origins
  let root:=CurrentCallSpatialEntryControl.root initial #[] place model.noDataRace
  let adjusted : Immediate Provenance:=(DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base (.pointer (Pointer.new (.concrete sourceId tracker.global.nextPointerTag) (Size.ofBytes (sourceBase+start)))) 0 ActualReferenceMetadata.reference).imm
  have installed' : frame=PositiveRootInstalledFrame.installed root adjusted count {} sourceId tracker.global.nextPointerTag physical.id node.tag := by
    rw [nodeTag]
    exact installed
  obtain ⟨oldThread,oldActive,_⟩:=stackReady
  let thread:={oldThread with topUserRelevantFrame:=some 0}
  have active : machine.threads.activeThread?=some thread := by
    rw [threads]
    exact PushThread.cache_top_active (CallEntryFacts.freshRoot initial).1 oldThread 0 oldActive
  have currentAt : Q.allocation.extra.nodes.get Q.pointer.grant=some node := by rw [grantQ];exact nodeAt
  have currentActive : GeneralBorrowFreshActiveWithin.ActiveWithin Q.allocation.extra Q.pointer.grant .Write window.offset (window.offset+1) := by
    rw [grantQ,windowOffset];exact activity
  have currentEdge : Q.precise.completion.parents[Q.pointer.grant.toNat]?=some (some B.pointer.grant) := by rw [grantQ];exact edge
  obtain ⟨qi,qn,qt,qa,qtag,_,qh,qinactive⟩:=sourceLeaf
  have currentSourceRoom : sourceEntry.allocation.extra.nodes.size+2≤4294967295 := by have growth:=facts.sourceGrowth;omega
  have helperRoom : output.global.nextPointerTag.value.toNat+1<18446744073709551615 := by rw [facts.counter];omega
  obtain ⟨final,trace,terminal,emptyStack⟩:=CurrentCallEmptyLiveDifferentNonzeroFinish.finish options limits remaining span place B Q window windowBinding windowId
    (congrArg UInt64.toNat windowOffset) (windowPointer.trans pointer) windowAllocation parentIssued parentBinding runtimeQ rootsQ shortQ
    ⟨physical.id,output.tag,concreteQ⟩ node currentAt hidden currentActive sourceId sourceEntry sourceLive different facts.sourceRuntime currentSourceRoom
    tracker.global.nextPointerTag qi qn qt qa qh (CurrentCallResourceEmptyRootRelease.quiescent_of_inactive _ _ _ qinactive) sourceHidden
    sourceBase start count nonzero countNonzero facts.cached root (RootEntryFrame.raw_locals _ _ _) frame installed' rfl rfl rfl modelAfter facts.origins tracked thread active rfl
    currentEdge windowReady helperRoom dynamicFuel validationFuel budget dynamicEq validationEq dispatchEq
  let start:=Storage.withCurrent #[] frame machine
  let context : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit:=⟨config options (remaining+1) span,limits,fun _ _=>True⟩
  have callEntry : CallSafety.IsCallEntry 1 start:=⟨by decide,rfl⟩
  have past : CallSafety.pastCallBoundary 1 final:=by change final.stack.frames.size<1;rw [emptyStack];decide
  exact ⟨start,final,entered,trace,terminal,emptyStack,
    SuccessfulTrace.no_errors context 1 start final callEntry trace past,
    SuccessfulTrace.no_ub context 1 start final callEntry trace past,
    SuccessfulTraceTerminal.prefix_step_success trace terminal⟩

end
end DuplicatePrefix.CurrentCallEmptyLiveNonzeroSafety
