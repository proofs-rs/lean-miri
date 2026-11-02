import duplicate_prefix.S02SeparateDestinationZeroCore
import duplicate_prefix.S02SameDestinationActivePacket
import duplicate_prefix.S02SameDestinationPhysicalInstalled
import duplicate_prefix.S02SameDestinationHiddenFrame
import duplicate_prefix.S02SeparateDestinationPhysicalEntry
import duplicate_prefix.S02SeparateDestinationEntryIdentity
import duplicate_prefix.S03ReturnProtectionRaw

import duplicate_prefix.S02SameDestinationZeroCore

namespace DuplicatePrefix.S02SameDestinationRejectedResultCore
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The original call contract supplies all borrow and physical facts at the
actual installed frame for a positive concrete source and same-allocation concrete
return place. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag)
    (givenReference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new (.concrete id tag) (Size.ofBytes address)) len) :
    ∃ (frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      ∃ packet : S02SameDestinationZeroCore.Packet frame machine place, packet.sourceNode.tag = packet.sourceTag ∧ packet.sourceOffset = givenReference.offset ∧ packet.sourceLen = len ∧
      GeneralBorrowWildcardParentTagOrder.ParentTagOrder packet.destination.entry.allocation.extra := by
  obtain ⟨reference,firstFresh,destination,secondFresh,updated,sourceChild,child,sourceRaw,
      sourceBefore,sourceNode,node,parent,actual,sameId,destOffset,sourceBeforeTagged,sourceBeforePresent,
      sourceBeforeSame,sourceBeforeLeaf,sourceBeforeHidden,sourceBeforeActivity,sourceTagged,sourcePresent,
      sourceSame,sourceHidden,present,same,leaf,hidden,parentSource,edge,childrenDifferent,roots,short,
      extra,bytes,length,mutable,runtime,order,⟨sourcePositive⟩,tagged,⟨positive⟩,active,sourceActive⟩ :=
    S02SameDestinationActivePacket.enters id tag address len count input nonempty sameAllocation returnTag returnConcrete
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before)
    reference.tracker firstFresh reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
      (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result
    (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
      reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra
    destination.tracker returnTag destination.offset 1
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
  let tracker := TypedBorrowSteps.registeredTracker
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh) destination.tracker.global.nextPointerTag
  let global := TypedBorrowSteps.registeredGlobal
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh) destination.tracker.global.nextPointerTag
  obtain ⟨physicalFrame,physicalMachine,physicalActual,⟨physical⟩⟩ :=
    S02SameDestinationPhysicalInstalled.enters id tag address len count input nonempty sameAllocation returnTag returnConcrete
  have machineEq : physicalMachine = after.machine := congrArg (fun s : RootState => s.machine)
    (EStateM.Result.ok.inj (physicalActual.symm.trans actual)).2
  rw [machineEq] at physical
  have binding := reference.binding
  simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
  have idEq : id = reference.id := binding.1
  have destId : destination.id = input.contract.destination.id := sameId.trans (idEq.symm.trans sameAllocation)
  have concrete : destination.pointer.provenance = .concrete destination.id returnTag := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    rw [Option.some.inj provenance,destId]
    exact returnConcrete
  obtain ⟨physicalId,physicalTag⟩ := S02SeparateDestinationPhysicalIdentity.original destination physical returnTag concrete
  have physicalEntry : physical.entry = {destination.entry with allocation := updated} :=
    S02SeparateDestinationPhysicalEntry.updated_row destination #[] changed owned secondFresh tree updated physical returnTag concrete
  have destEntry : destination.entry = {reference.entry with allocation := (reference.entry.allocation.setExtra
      (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len))} := by
    have live : current.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,
        {reference.entry with allocation := (reference.entry.allocation.setExtra
          (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len))}) :=
      MemoryCopyBridge.live_lookup_replaced (RawRootInvocation.machine #[] before).memory reference.id _
    have original := destination.live
    rw [sameId] at original
    exact congrArg Prod.snd (Option.some.inj (original.symm.trans live))
  obtain ⟨currentRuntime,currentRoots,currentOrder,headroom,_⟩ :=
    S02SameDestinationReady.local_facts_after_argument input reference firstFresh destination destEntry
  obtain ⟨returnRaw,parentTagEq,offsetRaw,lenRaw,selectedEq,maximumEq⟩ :=
    S03ReturnProtectionRaw.packet destination currentRuntime currentRoots currentOrder headroom secondFresh returnTag concrete
  have shape := S02SeparateDestinationWrittenShape.run destination currentRuntime currentRoots currentOrder headroom secondFresh returnTag concrete
  have originalTagged : destination.entry.allocation.extra.indexOfTag returnTag = some parent := by
    have h := destination.binding
    simp only [DuplicatePrefixReferenceInput.Binding,concrete] at h
    obtain ⟨_,p,source,tagged⟩ := h
    have equal : p = parent := Option.some.inj (source.symm.trans parentSource)
    simpa only [equal] using tagged
  have parentTagged : updated.extra.indexOfTag returnTag = some parent := by
    rw [extra,shape.2]
    exact originalTagged
  have parentEq : physical.parent = parent := by
    have tagged := physical.tagged
    rw [physicalEntry,physicalTag] at tagged
    exact Option.some.inj (tagged.symm.trans parentTagged)
  have baseEq : physical.base = destination.base := by
    have h := physical.cachedBase
    change current.user.addresses.baseAddr.find? (fun row => row.allocId == physical.id) = _ at h
    rw [physicalId] at h
    exact congrArg AllocAddresses.BaseAddressEntry.address (Option.some.inj (h.symm.trans destination.cachedBase))
  have offsetEq : physical.offset = destination.offset := by
    have h := congrArg (fun ptr : Pointer (Option Provenance) => ptr.offset.bytes)
      (physical.physicalPointer.symm.trans destination.physicalPointer)
    simp only [Pointer.withOptionalProvenance] at h
    rw [physical.pointerAddress,destination.pointerAddress,baseEq] at h
    bv_decide
  have frameTracked : installed.extra.borrowTracker = some borrowFrame := by rfl
  have enabled : after.machine.borrowTracker = some tracker := by rfl
  have ownedTags : borrowFrame.protectedTags =
      #[(physical.id,reference.tracker.global.nextPointerTag),(physical.id,destination.tracker.global.nextPointerTag)] := by
    rw [physicalId]
    change #[(reference.id,reference.tracker.global.nextPointerTag),(destination.id,destination.tracker.global.nextPointerTag)] = _
    rw [sameId]
  have runtimePhysical : DuplicatePrefixBorrowContract.RuntimeFacts physical.entry.allocation.extra tracker.global := by
    rw [physicalEntry,extra]
    exact runtime
  have sourceTaggedPhysical : physical.entry.allocation.extra.indexOfTag reference.tracker.global.nextPointerTag = some sourceChild := by
    rw [physicalEntry,extra];exact sourceTagged
  have sourcePresentPhysical : physical.entry.allocation.extra.nodeAt sourceChild = some sourceNode := by
    rw [physicalEntry,extra];exact sourcePresent
  have taggedPhysical : physical.entry.allocation.extra.indexOfTag destination.tracker.global.nextPointerTag = some child := by
    rw [physicalEntry,extra];exact tagged
  have presentPhysical : physical.entry.allocation.extra.nodeAt child = some node := by
    rw [physicalEntry,extra];exact present
  have hiddenFrame := S02SameDestinationHiddenFrame.of_hidden physical.entry.allocation.extra tracker.global borrowFrame
    physical.id physical.id reference.tracker.global.nextPointerTag destination.tracker.global.nextPointerTag child node ownedTags
    runtimePhysical sourceChild sourceNode sourceTaggedPhysical sourcePresentPhysical sourceHidden taggedPhysical presentPhysical hidden
  have separateWindows := S02SameDestinationLiveTransport.actual_reference_disjoint id tag address len input nonempty sameAllocation reference
  have sourceStop : (reference.offset+len).toNat = reference.offset.toNat+len.toNat := by
    rw [UInt64.toNat_add,Nat.mod_eq_of_lt]
    exact Nat.lt_of_le_of_lt reference.borrow.bounds reference.entry.allocation.extra.locations.size.bytes.toNat_lt
  have returnStop : (physical.offset+1).toNat = physical.offset.toNat+1 := by
    have bound : physical.offset.toNat+1 < 2^64 := Nat.lt_of_le_of_lt physical.bounds physical.capacity.toNat_lt
    rw [UInt64.toNat_add,show (1 : UInt64).toNat = 1 from rfl,Nat.mod_eq_of_lt bound]
  have separation : (reference.offset+len).toNat ≤ physical.offset.toNat ∨ (physical.offset+1).toNat ≤ reference.offset.toNat := by
    rw [sourceStop,returnStop,offsetEq,destOffset]
    exact separateWindows
  have referenceId : reference.id = givenReference.id := by
    have first := reference.binding
    have second := givenReference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at first second
    exact first.1.symm.trans second.1
  have referenceBase : reference.base = givenReference.base := by
    have cached := reference.cachedBase
    rw [referenceId] at cached
    have same := Option.some.inj (cached.symm.trans givenReference.cachedBase)
    exact congrArg AllocAddresses.BaseAddressEntry.address same
  have referenceOffset : reference.offset = givenReference.offset := by
    have first := reference.pointerAddress
    have second := givenReference.pointerAddress
    rw [referenceBase] at first
    have sums : givenReference.base+reference.offset = givenReference.base+givenReference.offset := first.symm.trans second
    bv_decide
  exact ⟨installed,after.machine,actual,{
    tracker := tracker,borrowFrame := borrowFrame,destination := physical,
    sourceTag := reference.tracker.global.nextPointerTag,sourceChild := sourceChild,
    sourceSelected := sourceRaw.selected,sourceMaximum := sourceRaw.maximum,
    sourceOffset := reference.offset,sourceLen := len,sourceNode := sourceNode,
    sourceTagged := sourceTaggedPhysical,sourcePresent := sourcePresentPhysical,sourceHidden := sourceHidden,
    sourceRuntime := runtimePhysical,sourcePositive := by rw [physicalEntry,extra];exact sourcePositive,
    sourceDistinct := by rw [physicalEntry,extra];exact roots,
    sourceOrder := by intro _ _;rw [physicalEntry,extra];exact order,
    sourceShort := by rw [physicalEntry,extra];exact short,
    sourceActivity := by rw [physicalEntry,extra];exact sourceActive,
    returnTag := destination.tracker.global.nextPointerTag,child := child,selected := returnRaw.selected,maximum := destination.maximum,
    returnNode := node,enabled := enabled,frameTracked := frameTracked,owned := ownedTags,
    returnTagged := taggedPhysical,returnPresent := presentPhysical,returnSame := same,
    returnEdge := by rw [parentEq];exact edge,returnHidden := hidden,hiddenFrame := hiddenFrame,
    runtime := runtimePhysical,positive := by rw [physicalEntry,extra,offsetEq,←selectedEq];exact positive,
    distinct := by rw [physicalEntry,extra];exact roots,
    order := by intro _ _;rw [physicalEntry,extra];exact order,
    short := by rw [physicalEntry,extra];exact short,
    activity := by rw [physicalEntry,extra,offsetEq];exact active,
    returnLeaf := leaf,childrenDifferent := Ne.symm childrenDifferent,disjoint := separation},sourceSame,referenceOffset,rfl,by rw [physicalEntry,extra];exact order⟩

end
end DuplicatePrefix.S02SameDestinationRejectedResultCore

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationRejectedResultCore.enters) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved same destination zero core dependency {dependency}"
