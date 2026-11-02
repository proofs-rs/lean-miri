import duplicate_prefix.CurrentCallEmptyNonliveSafety
import duplicate_prefix.CurrentCallEmptyNonliveEncoding
import duplicate_prefix.S03NonliveMetadataTag
namespace DuplicatePrefix.CurrentCallEmptyWildcardNonliveSafety
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
open CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps GeneralBorrowFnEntryRegistration
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
noncomputable section
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span before) (enabled : before.borrowTracker=some tracker)
    (stackReady : CurrentCallPush.StackReadiness before #[])
    (sourceId : AllocId) (base sourceOffset count : UInt64) (nonnull : base+sourceOffset≠0)
    (cached : before.user.addresses.baseAddr.find? (fun row=>row.allocId==sourceId)=some ⟨sourceId,base⟩)
    (metadata : DuplicatePrefixEmptyReferenceInput.Metadata before.memory sourceId none)
    (absent : before.memory.live.find? (fun row=>row.1==sourceId)=none)
    (info : AllocationInfo) (known : before.memory.getAllocInfo sourceId=.ok info)
    (geometry : WildcardGeneralHitReborrow.Geometry before.user.addresses.intToPtrMap (base+sourceOffset) base sourceId info.size)
    (nonstrict : before.user.addresses.provenanceMode≠.strict)
    (exposed : before.user.addresses.exposed.contains sourceId=true)
    (coherent : GlobalAddressRecurringFormation.State before.memory before.user.addresses)
    (place : MPlaceTy Provenance) (physical : CandidateCurrentBoolUninitWrite.PhysicalWindow before place)
    (data : Identities) (owner : Nat) (B : UniformWindow before tracker data owner physical.id physical.offset.toNat 1 .ret)
    (pointer : physical.pointer=B.pointer.value) (allocation : physical.entry.allocation=B.allocation)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts B.allocation.extra tracker.global)
    (binding : CandidateCallBindings.WindowBinding before physical.pointer physical.id physical.offset.toNat 1)
    (distinct : B.allocation.extra.roots.toList.Nodup)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+6<18446744073709551615)
    (nodeRoom : B.allocation.extra.nodes.size+1<65536)
    (ready : CurrentCallBoolProtection.WindowReady before physical.id physical.offset.toNat 1)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins before.user.payload.payload.user.types)
    (dynamicFuel validationFuel budget : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1)
    (validationEq : options.limits.validation=validationFuel+1) (dispatchEq : limits.callDispatch=budget+1) :
    DuplicatePrefixArgumentCallResult.Result options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes (base+sourceOffset)))) 0 count place := by
  let parentTag:=tracker.global.nextPointerTag
  have concreteMetadata:=S03NonliveMetadataTag.changeTag before.memory sourceId none (some parentTag) metadata absent
  have result:=CurrentCallEmptyNonliveSafety.invoke options limits remaining span before tracker model enabled stackReady
    sourceId parentTag base sourceOffset count nonnull cached concreteMetadata absent place physical data owner B pointer allocation runtime binding distinct
    tagRoom nodeRoom ready origins dynamicFuel validationFuel budget dynamicEq validationEq dispatchEq
  obtain ⟨actualInfo,actualKnown,notLive⟩:=S03NonliveEmptyMetadata.known before.memory sourceId none metadata absent
  have sameInfo : actualInfo=info:=Except.ok.inj (actualKnown.symm.trans known)
  have allocLive : before.memory.isAllocLive sourceId=true:=coherent.live.2 sourceId (Array.contains_iff_mem.mp exposed)
  have fresh : tracker.global.nextPointerTag.value<18446744073709551615:=UInt64.lt_iff_toNat_lt.mpr (by
    change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)
  obtain ⟨ctx⟩:=(DuplicatePrefixCallModel.contexts options remaining span before model).1
  have equal:=CurrentCallEmptyNonliveEncoding.call_equal options limits remaining span ctx model.debugOff model.nullComparator
    dynamicFuel validationFuel dynamicEq validationEq sourceId parentTag tracker base sourceOffset count nonnull before model.ghostOff model.shallow
    cached info known (by rw [←sameInfo];exact notLive) geometry nonstrict exposed allocLive enabled fresh model.noDataRace model.metadata
    (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata origins) place stackReady
  obtain ⟨start,final,entered,trace,terminal,empty,noErrors,noUb,prefixes⟩:=result
  refine ⟨start,final,?_,trace,terminal,empty,noErrors,noUb,prefixes⟩
  exact equal.trans entered
end
end DuplicatePrefix.CurrentCallEmptyWildcardNonliveSafety
