import duplicate_prefix.CurrentCallEmptyLiveNonzeroSafety
import duplicate_prefix.CurrentCallEmptyLiveZeroSafety
import duplicate_prefix.DuplicatePrefixArgumentCallResult
import duplicate_prefix.PushThread
namespace DuplicatePrefix.CurrentCallEmptyLiveSafety
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
    (count : UInt64) (budget : Nat) (dispatchEq : limits.callDispatch=budget+1) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span initial (.pointer (Pointer.new (.concrete physical.id parentTag) (Size.ofBytes (physical.base+start)))) 0 count place := by
  by_cases countZero : count=0
  · subst count
    exact CurrentCallEmptyLiveZeroSafety.concrete_same options limits remaining span initial tracker model enabled stackReady place physical data owner B pointer allocation runtime binding distinct parentTag parent parentNode tagged parentAt start nonzero (by omega) (by omega) ready dynamicFuel validationFuel dynamicEq validationEq origins
  · have countNonzero : count≠0:=countZero
    exact CurrentCallEmptyLiveNonzeroSafety.concrete_same options limits remaining span initial tracker model enabled stackReady place physical data owner B pointer allocation runtime binding distinct parentTag parent parentNode tagged parentAt start nonzero tagRoom nodeRoom ready dynamicFuel validationFuel dynamicEq validationEq origins count countNonzero budget dispatchEq

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
    (count : UInt64) (budget : Nat) (dispatchEq : limits.callDispatch=budget+1) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span initial (.pointer (Pointer.new (.concrete sourceId parentTag) (Size.ofBytes (sourceBase+start)))) 0 count place := by
  by_cases countZero : count=0
  · subst count
    exact CurrentCallEmptyLiveZeroSafety.concrete_different options limits remaining span initial tracker model enabled stackReady place physical data owner B pointer allocation runtime binding distinct sourceId different entry sourceLive sourceBase sourceCached sourceRuntime (by omega) parentTag parent parentNode tagged parentAt start nonzero (by omega) (by omega) ready dynamicFuel validationFuel dynamicEq validationEq origins
  · have countNonzero : count≠0:=countZero
    exact CurrentCallEmptyLiveNonzeroSafety.concrete_different options limits remaining span initial tracker model enabled stackReady place physical data owner B pointer allocation runtime binding distinct sourceId different entry sourceLive sourceBase sourceCached sourceRuntime sourceRoom parentTag parent parentNode tagged parentAt start nonzero tagRoom nodeRoom ready dynamicFuel validationFuel dynamicEq validationEq origins count countNonzero budget dispatchEq

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
    (count : UInt64) (budget : Nat) (dispatchEq : limits.callDispatch=budget+1) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span initial (.pointer (Pointer.new (.wildcard) (Size.ofBytes (physical.base+start)))) 0 count place := by
  by_cases countZero : count=0
  · subst count
    exact CurrentCallEmptyLiveZeroSafety.wildcard_same options limits remaining span initial tracker model enabled stackReady place physical data owner B pointer allocation runtime binding distinct start nonzero addressMode inverse exposed (by omega) (by omega) ready dynamicFuel validationFuel dynamicEq validationEq origins
  · have countNonzero : count≠0:=countZero
    exact CurrentCallEmptyLiveNonzeroSafety.wildcard_same options limits remaining span initial tracker model enabled stackReady place physical data owner B pointer allocation runtime binding distinct start nonzero addressMode inverse exposed tagRoom nodeRoom ready dynamicFuel validationFuel dynamicEq validationEq origins count countNonzero budget dispatchEq

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
    (count : UInt64) (budget : Nat) (dispatchEq : limits.callDispatch=budget+1) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span initial (.pointer (Pointer.new (.wildcard) (Size.ofBytes (sourceBase+start)))) 0 count place := by
  by_cases countZero : count=0
  · subst count
    exact CurrentCallEmptyLiveZeroSafety.wildcard_different options limits remaining span initial tracker model enabled stackReady place physical data owner B pointer allocation runtime binding distinct sourceId different entry sourceLive sourceBase sourceCached sourceRuntime (by omega) start nonzero addressMode inverse exposed (by omega) (by omega) ready dynamicFuel validationFuel dynamicEq validationEq origins
  · have countNonzero : count≠0:=countZero
    exact CurrentCallEmptyLiveNonzeroSafety.wildcard_different options limits remaining span initial tracker model enabled stackReady place physical data owner B pointer allocation runtime binding distinct sourceId different entry sourceLive sourceBase sourceCached sourceRuntime sourceRoom start nonzero addressMode inverse exposed tagRoom nodeRoom ready dynamicFuel validationFuel dynamicEq validationEq origins count countNonzero budget dispatchEq

end
end DuplicatePrefix.CurrentCallEmptyLiveSafety
