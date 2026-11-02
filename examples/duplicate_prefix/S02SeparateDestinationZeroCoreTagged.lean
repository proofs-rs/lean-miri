import duplicate_prefix.S02SeparateDestinationZeroCore
import duplicate_prefix.S02SeparateDestinationBothPhysicalReadyInstalled
import duplicate_prefix.S02SeparateDestinationPhysicalEntry
import duplicate_prefix.S02SeparateDestinationEntryIdentity
import duplicate_prefix.S03ReturnProtectionRaw

namespace DuplicatePrefix.S02SeparateDestinationZeroCoreTagged
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The original call contract supplies all borrow and physical facts at the
actual installed frame for a positive concrete source and distinct concrete
return place. -/
theorem enters
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (different : id ≠ input.contract.destination.id)
    (returnTag : BorTag)
    (returnConcrete : input.contract.destination.pointer.provenance =
      .concrete input.contract.destination.id returnTag) :
    ∃ (frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
      ∃ packet : S02SeparateDestinationZeroCore.Packet frame machine place,
        packet.sourceNode.tag = packet.sourceTag := by
  obtain ⟨reference,firstFresh,destination,secondFresh,updated,child,actual,extra,tagged,runtime,
      ⟨positive⟩,active,parent,node,parentTagged,present,same,edge,leaf,hidden,hiddenFrame,
      sourceChild,sourceNode,sourceRaw,sourceTracker,sourceEnabled,sourceLive,sourceTagged,
      sourcePresent,sourceSame,sourceHidden,sourceRuntime,⟨sourcePositive⟩,sourceActive,sourceRoots,
      sourceOrder,sourceShort,⟨physical⟩,updatedRoots,updatedOrder,updatedShort⟩ :=
    S02SeparateDestinationBothPhysicalReadyInstalled.enters_ready id tag address len count input
      nonempty different returnTag returnConcrete
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
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
  let sourceTree := GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra
    reference.tracker tag reference.offset len
  let sourceEntry := {reference.entry with allocation := reference.entry.allocation.setExtra sourceTree}
  let global := TypedBorrowSteps.registeredGlobal
    (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  obtain ⟨idEq,destId,destEntry,concrete⟩ :=
    S02SeparateDestinationEntryIdentity.from_contract id tag address len input reference firstFresh
      destination different returnTag returnConcrete
  obtain ⟨physicalId,physicalTag⟩ :=
    S02SeparateDestinationPhysicalIdentity.original destination physical returnTag concrete
  have physicalEntry : physical.entry = {destination.entry with allocation := updated} :=
    S02SeparateDestinationPhysicalEntry.updated_row destination #[] changed owned secondFresh tree
      updated physical returnTag concrete
  have parentEq : physical.parent = parent := by
    have p := physical.tagged
    rw [physicalEntry,physicalTag] at p
    exact Option.some.inj (p.symm.trans parentTagged)
  have separate : physical.id ≠ reference.id := by
    rw [physicalId,destId,←idEq]
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
    S02SeparateDestinationReady.local_facts_after_argument input reference firstFresh destination destEntry
  have raw := S03ReturnProtectionRaw.packet destination currentRuntime roots order headroom secondFresh
    returnTag concrete
  obtain ⟨returnRaw,_,_,_,selectedEq,maximumEq⟩ := raw
  have taggedPhysical : physical.entry.allocation.extra.indexOfTag returnTag = some parent := by
    rw [physicalEntry]
    exact parentTagged
  have presentPhysical : physical.entry.allocation.extra.nodeAt child = some node := by
    rw [physicalEntry]
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
  exact ⟨installed,after.machine,actual,{
    tracker := sourceTracker
    borrowFrame := borrowFrame
    destination := physical
    sourceId := reference.id
    sourceEntry := sourceEntry
    separate := separate
    sourceLive := sourceLive
    sourceTag := reference.tracker.global.nextPointerTag
    sourceChild := sourceChild
    sourceSelected := sourceRaw.selected
    sourceMaximum := sourceRaw.maximum
    sourceOffset := reference.offset
    sourceLen := len
    sourceNode := sourceNode
    sourceTagged := sourceTagged
    sourcePresent := sourcePresent
    sourceHidden := sourceHidden
    sourceRuntime := sourceRuntime
    sourcePositive := sourcePositive
    sourceDistinct := sourceRoots
    sourceOrder := sourceOrder
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
    distinct := by rw [physicalEntry];exact updatedRoots
    order := by rw [physicalEntry];intro valid _;exact updatedOrder
    short := by rw [physicalEntry];exact updatedShort
    activity := by rw [physicalEntry,offsetEq];exact active
  },sourceSame⟩

end
end DuplicatePrefix.S02SeparateDestinationZeroCoreTagged

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SeparateDestinationZeroCoreTagged.enters) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate destination tagged zero-core dependency {dependency}"
