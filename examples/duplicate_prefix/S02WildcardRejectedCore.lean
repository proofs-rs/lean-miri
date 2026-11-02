import duplicate_prefix.S02WildcardBothInstalledFrame
import duplicate_prefix.S02SeparateDestinationZeroCore
import duplicate_prefix.S02WildcardSharedTagMargin
import duplicate_prefix.GeneralBorrowRawShared
import duplicate_prefix.S02SeparateDestinationPhysicalEntry
import duplicate_prefix.S02SeparateDestinationPhysicalIdentity
import duplicate_prefix.S02WildcardSeparateConcreteHiddenFrame
import duplicate_prefix.S02SeparateDestinationWrittenReady
import duplicate_prefix.S03ReturnProtectionRaw

namespace DuplicatePrefix.S02WildcardRejectedCore
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The exact wildcard installed packet also exposes the raw shared-Ref input
needed to execute the rejected count branch. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
    ∃ (frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      ∃ (packet : S02SeparateDestinationZeroCore.Packet frame machine place)
        (raw : GeneralBorrowRawShared.Input packet.sourceEntry.allocation.extra packet.tracker.global),
        let root := RawRootInvocation.root before place input.contract.model.noDataRace
        let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
            (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
        frame = PositiveRootInstalledFrame.installed root adjusted count {}
          reference.id reference.tracker.global.nextPointerTag
          packet.destination.id packet.returnTag ∧
        machine.user = (RawRootInvocation.machine #[] before).user ∧
        machine.threads = (RawRootInvocation.machine #[] before).threads ∧
        machine.dataRace = (RawRootInvocation.machine #[] before).dataRace ∧
        packet.tracker.retagMode = .Default ∧
        raw.parentTag = reference.tracker.global.nextPointerTag ∧
        raw.parent = packet.sourceChild ∧ raw.offset = reference.offset ∧ raw.len = len := by
  obtain ⟨reference,output,firstFresh,ready⟩ :=
    S02WildcardBothInstalledFrame.installed address len count input nonempty returnTag returnConcrete
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨installedFrame,installedMachine,sourceEntry,sourceChild,sourceNode,sourceTracker,
    actual,sourceEnabled,sourceLive,sourceTagged,sourcePresent,sourceSame,sourceParentless,
    sourceLeaf,sourceHidden,sourceRuntime,⟨sourcePositive⟩,sourceActive,sourceRoots,
    sourceOrder,sourceShort,⟨physical⟩,destination,secondFresh,updated,child,
    frameEq,machineEq,extra,tagged,runtime,⟨positive⟩,active,hiddenFrame⟩ := ready different
  let current := GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
    (RawRootInvocation.machine #[] before) reference.tracker firstFresh
    reference.id reference.entry output.child.tree
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
    destination.tracker returnTag destination.offset 1
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
  let global := TypedBorrowSteps.registeredGlobal
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  subst installedFrame
  subst installedMachine
  have destId : destination.id = input.contract.destination.id := by
    have pointer := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) pointer
    simp only [Pointer.withOptionalProvenance] at provenance
    have same := Option.some.inj provenance
    have concrete : destination.pointer.provenance = .concrete input.contract.destination.id returnTag :=
      same.trans returnConcrete
    have binding := destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at binding
    exact binding.1.symm
  have destEntry : destination.entry = input.contract.destination.entry := by
    have other : reference.id ≠ destination.id := by rw [destId];exact different
    have live : current.memory.live.find? (fun row => row.1 == destination.id) =
        some (destination.id,input.contract.destination.entry) := by
      change (RetagEntry.updatedMemory (RawRootInvocation.machine #[] before).memory
        reference.id reference.entry output.child.tree).live.find?
          (fun row => row.1 == destination.id) = _
      rw [S02SeparateDestinationTransport.other_live _ _ _ _ _ other]
      have preserved := (RawRootInvocation.preservation #[] before).1
      rw [preserved,destId]
      exact input.contract.destination.live
    exact congrArg Prod.snd (Option.some.inj (destination.live.symm.trans live))
  have concrete : destination.pointer.provenance = .concrete destination.id returnTag := by
    have pointer := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) pointer
    simp only [Pointer.withOptionalProvenance] at provenance
    rw [Option.some.inj provenance,destId]
    exact returnConcrete
  obtain ⟨_hiddenRuntime,parent,hiddenChild,node,parentTagged,childTagged,present,same,edge,leaf,hidden,_hidden⟩ :=
    S02WildcardSeparateConcreteHiddenFrame.written_hidden address len input reference output
      firstFresh destination destEntry secondFresh returnTag concrete
  let written := (tree.performBorrowAccessRange
    (.concrete destination.tracker.global.nextPointerTag) (Size.ofBytes destination.offset)
    (Size.ofBytes 1) .Write global.protectedTags .VisitChildrenOfAccessed).tree
  have childEq : child = hiddenChild := by
    have updatedTagged : updated.extra.indexOfTag destination.tracker.global.nextPointerTag =
        some hiddenChild := by
      rw [extra]
      exact childTagged
    exact Option.some.inj (tagged.symm.trans updatedTagged)
  subst hiddenChild
  obtain ⟨physicalId,physicalTag⟩ :=
    S02SeparateDestinationPhysicalIdentity.original destination physical returnTag concrete
  have physicalEntry : physical.entry = {destination.entry with allocation := updated} :=
    S02SeparateDestinationPhysicalEntry.updated_row destination #[] changed owned secondFresh tree
      updated physical returnTag concrete
  have parentEq : physical.parent = parent := by
    have p := physical.tagged
    rw [physicalEntry,physicalTag] at p
    have taggedUpdated : updated.extra.indexOfTag returnTag = some parent := by
      rw [extra]
      exact parentTagged
    exact Option.some.inj (p.symm.trans taggedUpdated)
  have separate : physical.id ≠ reference.id := by
    rw [physicalId,destId]
    exact Ne.symm different
  have trackerEq : sourceTracker.global = global := by
    have registered : after.machine.borrowTracker =
        some (TypedBorrowSteps.registeredTracker
      (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
      destination.tracker.global.nextPointerTag) := by rfl
    have h := sourceEnabled.symm.trans registered
    exact congrArg MachineHooks.BorrowState.global (Option.some.inj h)
  have frameTracked : installed.extra.borrowTracker = some borrowFrame := by
    rfl
  have ownedTags : borrowFrame.protectedTags =
      #[(reference.id,reference.tracker.global.nextPointerTag),
        (physical.id,destination.tracker.global.nextPointerTag)] := by
    rw [physicalId]
    rfl
  obtain ⟨currentRuntime,roots,order,headroom,_⟩ :=
    S02WildcardSeparateDestinationReady.local_facts_after_argument input reference output firstFresh
      destination destEntry
  have raw := S03ReturnProtectionRaw.packet destination currentRuntime roots order headroom secondFresh
    returnTag concrete
  obtain ⟨returnRaw,_,_,_,selectedEq,maximumEq⟩ := raw
  obtain ⟨updatedRoots,updatedOrder,updatedShort⟩ :=
    S02SeparateDestinationWrittenReady.run destination currentRuntime roots order headroom
      secondFresh returnTag concrete
  have taggedPhysical : physical.entry.allocation.extra.indexOfTag returnTag = some parent := by
    rw [physicalEntry,extra]
    exact parentTagged
  have presentPhysical : physical.entry.allocation.extra.nodeAt child = some node := by
    rw [physicalEntry,extra]
    exact present
  have runtimePhysical : DuplicatePrefixBorrowContract.RuntimeFacts physical.entry.allocation.extra
      sourceTracker.global := by
    rw [physicalEntry,trackerEq]
    exact runtime
  have baseEq : physical.base = destination.base := by
    have addresses : after.machine.user.addresses = current.user.addresses := by rfl
    have h := physical.cachedBase
    rw [addresses,physicalId] at h
    exact congrArg AllocAddresses.BaseAddressEntry.address
      (Option.some.inj (h.symm.trans destination.cachedBase))
  have offsetEq : physical.offset = destination.offset := by
    have pointers := physical.physicalPointer.symm.trans destination.physicalPointer
    have address := congrArg (fun ptr : Pointer (Option Provenance) => ptr.offset.bytes) pointers
    simp only [Pointer.withOptionalProvenance] at address
    rw [physical.pointerAddress,destination.pointerAddress,baseEq] at address
    bv_decide
  have positivePhysical : DuplicatePrefixBorrowAuthorization.Positive physical.entry.allocation.extra
      sourceTracker.global.protectedTags (some child) (some returnRaw.selected)
      destination.maximum physical.offset 1 := by
    rw [physicalEntry,trackerEq,offsetEq]
    simpa only [selectedEq] using positive
  have updatedRoots' : updated.extra.roots.toList.Nodup := by rw [extra];exact updatedRoots
  have updatedOrder' : GeneralBorrowWildcardParentTagOrder.ParentTagOrder updated.extra := by
    rw [extra];exact updatedOrder
  have updatedShort' : updated.extra.nodes.size < 65536 := by rw [extra];exact updatedShort
  let packet : S02SeparateDestinationZeroCore.Packet installed after.machine place := {
    tracker := sourceTracker
    borrowFrame := borrowFrame
    destination := physical
    sourceId := reference.id
    sourceEntry := sourceEntry
    separate := separate
    sourceLive := sourceLive
    sourceTag := reference.tracker.global.nextPointerTag
    sourceChild := sourceChild
    sourceSelected := sourceChild
    sourceMaximum := some reference.tracker.global.nextPointerTag
    sourceOffset := reference.offset
    sourceLen := len
    sourceNode := sourceNode
    sourceTagged := sourceTagged
    sourcePresent := sourcePresent
    sourceHidden := sourceHidden
    sourceRuntime := sourceRuntime
    sourcePositive := sourcePositive
    sourceDistinct := sourceRoots
    sourceOrder := fun _ _ => sourceOrder
    sourceShort := sourceShort
    sourceActivity := sourceActive
    returnTag := destination.tracker.global.nextPointerTag
    child := child
    selected := returnRaw.selected
    maximum := destination.maximum
    returnNode := node
    enabled := sourceEnabled
    frameTracked := frameTracked
    owned := ownedTags
    returnTagged := by rw [physicalEntry];exact tagged
    returnPresent := presentPhysical
    returnSame := same
    returnEdge := by rw [parentEq];exact edge
    returnHidden := hidden
    hiddenFrame := by rw [physicalEntry];exact hiddenFrame
    runtime := runtimePhysical
    positive := positivePhysical
    distinct := by rw [physicalEntry];exact updatedRoots'
    order := by rw [physicalEntry];intro valid _;exact updatedOrder'
    short := by rw [physicalEntry];exact updatedShort'
    activity := by rw [physicalEntry,offsetEq];exact active
  }
  have tagMargin : global.nextPointerTag.value < 18446744073709551615 :=
    S02WildcardSharedTagMargin.after_second_protector input reference output firstFresh
      destination secondFresh
  let raw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra sourceTracker.global := {
    parentTag := reference.tracker.global.nextPointerTag
    parent := sourceChild
    selected := sourceChild
    maximum := some reference.tracker.global.nextPointerTag
    offset := reference.offset
    len := len
    tagged := sourceTagged
    positive := Classical.choice (GeneralBorrowReadRowRange.of_positive
      sourceEntry.allocation.extra sourceTracker.global.protectedTags sourceChild sourceChild
      (some reference.tracker.global.nextPointerTag) reference.offset len sourcePositive)
    distinct := sourceRoots
    order := fun _ _ => sourceOrder
    short := sourceShort
    nodeRoom := by omega
    tagRoom := by rw [trackerEq];exact tagMargin }
  have frameLiteral : installed = PositiveRootInstalledFrame.installed root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag
      packet.destination.id packet.returnTag := by
    change installed = PositiveRootInstalledFrame.installed root adjusted count {}
      reference.id reference.tracker.global.nextPointerTag physical.id
      destination.tracker.global.nextPointerTag
    rw [physicalId]
    rfl
  have rawUser : after.machine.user = (RawRootInvocation.machine #[] before).user := rfl
  have rawThreads : after.machine.threads = (RawRootInvocation.machine #[] before).threads := rfl
  have rawRace : after.machine.dataRace = (RawRootInvocation.machine #[] before).dataRace := rfl
  obtain ⟨originalTracker,originalEnabled,originalMode⟩ := input.contract.model.defaultTracker
  have referenceMode : reference.tracker.retagMode = .Default := by
    have same : reference.tracker = originalTracker :=
      Option.some.inj (reference.enabled.symm.trans originalEnabled)
    rw [same]
    exact originalMode
  have destinationMode : destination.tracker.retagMode = .Default := by
    have same : destination.tracker =
        ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
          reference.tracker.retagMode⟩ := by
      exact Option.some.inj (destination.enabled.symm.trans (show current.borrowTracker =
        some ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,
          reference.tracker.retagMode⟩ from rfl))
    rw [same]
    exact referenceMode
  have packetMode : packet.tracker.retagMode = .Default := by
    have registered : after.machine.borrowTracker =
        some (TypedBorrowSteps.registeredTracker
          (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
          destination.tracker.global.nextPointerTag) := rfl
    have same : sourceTracker = TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag :=
      Option.some.inj (sourceEnabled.symm.trans registered)
    change sourceTracker.retagMode = .Default
    rw [same]
    simpa only [TypedBorrowSteps.registeredTracker,ReferenceBorrowDriver.allocatedTracker] using
      destinationMode
  exact ⟨installed,after.machine,actual,packet,raw,frameLiteral,rawUser,rawThreads,rawRace,
    packetMode,rfl,rfl,rfl,rfl⟩

end
end DuplicatePrefix.S02WildcardRejectedCore

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardRejectedCore.enters) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard rejected-core dependency {dependency}"
