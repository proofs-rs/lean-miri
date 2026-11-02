import duplicate_prefix.S02WildcardSameDestinationRejectedProtect
import duplicate_prefix.S02WildcardSameDestinationInit
import duplicate_prefix.S02WildcardSharedTagMarginPlusOne
import duplicate_prefix.GeneralBorrowRawShared
import duplicate_prefix.PositiveRootInstalledFrame
namespace DuplicatePrefix.S02WildcardSameDestinationRejectedInitial
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The actual wildcard/same-allocation call retains the source identities and
numeric margins needed by the provenance-independent rejected body. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance} (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag) :
    ∃ reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new .wildcard (Size.ofBytes address)) len,
      reference.id = input.contract.destination.id →
    ∃ (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (packet : S02SameDestinationZeroCore.Packet frame machine place)
      (raw : GeneralBorrowRawShared.Input packet.destination.entry.allocation.extra packet.tracker.global),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),.Copy (EmptyRootArguments.second count)]
        false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      packet.destination.id = reference.id ∧ packet.sourceTag = reference.tracker.global.nextPointerTag ∧
      packet.sourceOffset = reference.offset ∧ packet.sourceLen = len ∧ packet.sourceNode.tag = packet.sourceTag ∧
      raw.parentTag = packet.sourceTag ∧ raw.parent = packet.sourceChild ∧ raw.selected = packet.sourceSelected ∧
      raw.maximum = packet.sourceMaximum ∧ raw.offset = reference.offset ∧ raw.len = len ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder packet.destination.entry.allocation.extra ∧
      packet.destination.entry.allocation.extra.locations.size = packet.destination.entry.allocation.byteSize ∧
      packet.destination.entry.allocation.extra.nodes.size+2 < 65536 ∧
      packet.destination.entry.allocation.extra.nodes.size+2 ≤ 4294967295 ∧
      packet.tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615 ∧
      packet.destination.entry.allocation.extra.nodes.size+8 < 65536 ∧
      packet.tracker.global.nextPointerTag.value.toNat+7 < 18446744073709551615 ∧
      frame = PositiveRootInstalledFrame.installed (RawRootInvocation.root before place input.contract.model.noDataRace)
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
        count {} reference.id reference.tracker.global.nextPointerTag packet.destination.id packet.returnTag ∧
      machine.user = (RawRootInvocation.machine #[] before).user ∧
      machine.threads = (RawRootInvocation.machine #[] before).threads ∧
      machine.dataRace = (RawRootInvocation.machine #[] before).dataRace ∧ packet.tracker.retagMode = .Default := by
  obtain ⟨reference,output,fresh,run,argument,ready⟩ :=
    S02WildcardSameDestinationInitAfterArgument.ready address len count input nonempty returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro same
  obtain ⟨data⟩ := ready same
  let destination := data.destination
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker fresh reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let args := (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
    reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {args with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  have frameBorrow : changed.extra.borrowTracker = some owned := by
    simp only [changed,args,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,RootFrameData.cache,
      RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,owned]
  have model := S02WildcardSeparateDestinationReady.model_after_argument input reference output fresh
  have extras : current.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
      some (destination.id,⟨none,#[]⟩) := by
    change (RawRootInvocation.machine #[] before).user.payload.payload.user.runtime.extras.allocations.find? _ = _
    rw [(RawRootInvocation.preservation #[] before).2.2.2.2.2.2.2.2,data.sameId,same]
    exact input.return_extras
  have ownedSource : owned.protectedTags = #[(destination.id,reference.tracker.global.nextPointerTag)] := by
    rw [data.sameId];rfl
  obtain ⟨updated,protect,packet,sourceTag,sourceChild,sourceSelected,sourceMaximum,sourceOffset,sourceLen,sourceSame,
    destId,destEntry,retTag,order,growth,extra⟩ := S02WildcardSameDestinationRejectedProtect.invoke
    (options := options) (remaining := remaining+1) (span := span) limits.retag current model place destination
    data.runtime data.distinct data.order data.headroom data.nextFresh returnTag data.concrete changed owned frameBorrow extras
    reference.tracker.global.nextPointerTag data.child data.child (some reference.tracker.global.nextPointerTag)
    reference.offset len data.node data.tagged data.present data.tag data.leaf data.hidden data.positive data.activity
    data.notSourceParent data.disjoint ownedSource
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker returnTag destination.offset 1
  let after := S04ProtectUninit.finished current place destination #[] changed owned data.nextFresh tree updated
  let installed := CallEntryFacts.doneRootFrame
    {TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag with location := .unwinding ⟨559⟩}
  have actual := S02WildcardFinishFromProtect.init address len count input nonempty reference output fresh argument
    destination data.nextFresh tree updated protect
  have destOriginal : destination.entry = {reference.entry with allocation := reference.entry.allocation.setExtra output.child.tree} := by
    have live := destination.live
    rw [data.sameId] at live
    exact congrArg Prod.snd (Option.some.inj (live.symm.trans (MemoryCopyBridge.live_lookup_replaced _ _ _)))
  obtain ⟨_,_,_,positive,runtime,distinct,short,nodes,tags⟩ :=
    S05WildcardEntryBridge.from_positive address len reference input.contract.runtime.toState input.contract.resources
  obtain ⟨created,createdRun,_,_,_,_,_,_,_,firstGrowth,_⟩ := GeneralBorrowRawWildcardFnEntryResources.invoke
    reference.entry.allocation.extra reference.tracker.global ({} : FrameState) reference.id runtime reference.offset len positive distinct short nodes tags
  have outputEq : created = output := Except.ok.inj (createdRun.symm.trans run)
  subst created
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList := Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have initialRoom := input.contract.resources.nodeRoom (reference.id,reference.entry) member
  have destGrowth : destination.entry.allocation.extra.nodes.size ≤ reference.entry.allocation.extra.nodes.size+1 := by rw [destOriginal];exact firstGrowth
  have postNodes : packet.destination.entry.allocation.extra.nodes.size+2 < 65536 := by
    rw [destEntry]
    change updated.extra.nodes.size+2 < 65536
    change reference.entry.allocation.extra.nodes.size+16 < 65536 at initialRoom
    omega
  have tagRoom := S02WildcardSharedTagMarginPlusOne.after_second_protector_plus_one input reference output fresh destination data.nextFresh
  have trackerEq : packet.tracker = TypedBorrowSteps.registeredTracker
      (ReferenceBorrowDriver.allocatedTracker destination.tracker data.nextFresh) destination.tracker.global.nextPointerTag :=
    Option.some.inj packet.enabled.symm
  change (TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker destination.tracker data.nextFresh)
    destination.tracker.global.nextPointerTag).global.nextPointerTag.value.toNat+1 < 18446744073709551615 at tagRoom
  rw [←trackerEq] at tagRoom
  let raw : GeneralBorrowRawShared.Input packet.destination.entry.allocation.extra packet.tracker.global := {
    parentTag := packet.sourceTag,parent := packet.sourceChild,selected := packet.sourceSelected,maximum := packet.sourceMaximum,
    offset := reference.offset,len := len,tagged := packet.sourceTagged,
    positive := by
      simpa only [sourceOffset,sourceLen] using Classical.choice (GeneralBorrowReadRowRange.of_positive _ _ _ _ _ _ _ packet.sourcePositive)
    distinct := packet.sourceDistinct,order := packet.sourceOrder,short := packet.sourceShort,
    nodeRoom := by omega,tagRoom := by apply UInt64.lt_iff_toNat_lt.mpr;change packet.tracker.global.nextPointerTag.value.toNat < 18446744073709551615;omega }
  have capacity : packet.destination.entry.allocation.extra.locations.size = packet.destination.entry.allocation.byteSize :=
    (congrArg Size.mk packet.destination.borrowSize).trans packet.destination.size.symm
  have refMode : reference.tracker.retagMode = .Default := by
    obtain ⟨other,enabled,mode⟩ := input.contract.model.defaultTracker
    have eq : reference.tracker = other := Option.some.inj (reference.enabled.symm.trans enabled)
    rw [eq];exact mode
  have destTracker : destination.tracker = ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global fresh,reference.tracker.retagMode⟩ :=
    Option.some.inj destination.enabled.symm
  have postReserve : packet.destination.entry.allocation.extra.nodes.size+8 < 65536 := by
    rw [destEntry]
    change updated.extra.nodes.size+8 < 65536
    change reference.entry.allocation.extra.nodes.size+16 < 65536 at initialRoom
    omega
  have tagReserve : packet.tracker.global.nextPointerTag.value.toNat+7 < 18446744073709551615 := by
    have refTracker : reference.tracker = input.contract.tracker := Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
    have reserve : reference.tracker.global.nextPointerTag.value.toNat+16 < 2^64 := by rw [refTracker];exact input.contract.resources.tagRoom
    have first := GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag fresh
    have second := GenericFunctionEntryNumerics.successor_value destination.tracker.global.nextPointerTag data.nextFresh
    have firstTag : destination.tracker.global.nextPointerTag.value.toNat = reference.tracker.global.nextPointerTag.value.toNat+1 := by
      rw [destTracker];exact first
    rw [trackerEq]
    change (TypedRetagEmpty.successorTag destination.tracker.global.nextPointerTag data.nextFresh).value.toNat+7 < 18446744073709551615
    omega
  refine ⟨installed,after.machine,packet,raw,actual,destId.trans data.sameId,sourceTag,sourceOffset,sourceLen,
    sourceSame.trans sourceTag.symm,rfl,rfl,rfl,rfl,rfl,rfl,?_,capacity,postNodes,by omega,tagRoom,postReserve,tagReserve,?_,rfl,rfl,rfl,?_⟩
  · rw [destEntry];exact order
  · rw [destId,retTag];rfl
  · rw [trackerEq]
    change destination.tracker.retagMode = .Default
    rw [destTracker];exact refMode
end
end DuplicatePrefix.S02WildcardSameDestinationRejectedInitial

#print axioms DuplicatePrefix.S02WildcardSameDestinationRejectedInitial.enters
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSameDestinationRejectedInitial.enters) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved wildcard same rejected initial dependency {dependency}"
