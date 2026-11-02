import duplicate_prefix.S02WildcardSourceWildcardNonzeroPrefixRun
import duplicate_prefix.S02WildcardSharedTagMargin
import duplicate_prefix.S05WildcardEntryBridge
import duplicate_prefix.GeneralBorrowRawShared

namespace DuplicatePrefix.S02WildcardSourceWildcardSharedPrefixExact
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- Exact installed wildcard/wildcard call supplies the source packet for the
real shared Ref, with physical capacity and allocator headroom. -/
theorem ready
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before}
    {place : MPlaceTy Provenance}
    (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0)
    (returnWildcard : input.contract.destination.pointer.provenance = .wildcard)
    (nonzero : count ≠ 0) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
      (Pointer.new .wildcard (Size.ofBytes address)) len),
      reference.id ≠ input.contract.destination.id →
      ∃ (output : GeneralBorrowForestFnEntry.Output)
        (firstFresh : reference.tracker.global.nextPointerTag.value < 18446744073709551615)
        (destination : DuplicatePrefixReturnPlaceInput.Input
          (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
            (RawRootInvocation.machine #[] before) reference.tracker firstFresh
            reference.id reference.entry output.child.tree) place)
        (secondFresh : destination.tracker.global.nextPointerTag.value < 18446744073709551615)
        (tree : BorrowTree) (updated : Allocation Provenance BorrowTree)
        (frame : CompilerFrameContext.ActualFrame)
        (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
        (source : LocalAllocation Provenance BorrowTree MiriMemoryKind)
        (tracker : MachineHooks.BorrowState)
        (raw : GeneralBorrowRawShared.Input source.allocation.extra tracker.global)
        (borrowFrame : FrameState)
        (returnPacket : S02ConcreteSourceWildcardReturnPacket.ReturnPacket machine place reference.id
          reference.tracker.global.nextPointerTag borrowFrame)
        (sourcePacket : S02WildcardSourceWildcardBothPacket.SourcePacket reference output machine),
        Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
          RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
          #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
            (.pointer (Pointer.new .wildcard (Size.ofBytes address))) len),
            .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
          ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] frame machine) ∧
        frame = PositiveRootInstalledFrame.installed
          (RawRootInvocation.root before place input.contract.model.noDataRace)
          (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
            (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
              (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
          count {} reference.id reference.tracker.global.nextPointerTag
          destination.id destination.tracker.global.nextPointerTag ∧
        machine.user = (RawRootInvocation.machine #[] before).user ∧
        machine.threads = (RawRootInvocation.machine #[] before).threads ∧
        machine.dataRace = (RawRootInvocation.machine #[] before).dataRace ∧
        destination.id = input.contract.destination.id ∧
        machine = (S04ProtectUninit.finished
          (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine
            (RawRootInvocation.machine #[] before) reference.tracker firstFresh
            reference.id reference.entry output.child.tree)
          place destination #[]
          { (RootArgumentsTwo.result
              (PositiveRootArguments.firstDone
                (RawRootInvocation.root before place input.contract.model.noDataRace)
                (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
                  (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
                    (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
                ({} : FrameState) reference.id reference.tracker.global.nextPointerTag) count).frame
            with location := .unwinding ⟨601⟩ }
          (({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag)
          secondFresh tree updated).machine ∧
        returnPacket.destination.id = destination.id ∧
        sourcePacket.entry = source ∧ sourcePacket.tracker = tracker ∧
        sourcePacket.child = raw.parent ∧ sourcePacket.child = raw.selected ∧
        raw.maximum = some reference.tracker.global.nextPointerTag ∧
        frame.extra.borrowTracker = some borrowFrame ∧
        machine.borrowTracker = some tracker ∧
        machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,source) ∧
        raw.parentTag = reference.tracker.global.nextPointerTag ∧
        raw.offset = reference.offset ∧ raw.len = len ∧
        source.allocation.extra.locations.size = source.allocation.byteSize ∧
        reference.offset.toNat+len.toNat ≤ source.allocation.byteSize.bytes.toNat ∧
        source.allocation.extra.nodes.size+2 < 65536 ∧
        tracker.global.nextPointerTag.value < 18446744073709551615 ∧
        ∃ prefixFrame,
          SuccessfulTrace.Trace (config options (remaining+1) span) limits
            (Storage.withCurrent #[] frame machine)
            (Storage.withCurrent #[] prefixFrame
              (RootZeroCompleteState.tick options remaining span machine)) ∧
          GenericFunctionEntryPrefix.Shape frame prefixFrame count := by
  obtain ⟨reference,output,firstFresh,ready⟩ :=
    S02WildcardSourceWildcardNonzeroPrefixRun.reaches_shared_site
      address len count input nonempty returnWildcard nonzero
  refine ⟨reference,?_⟩
  intro different
  obtain ⟨destination,secondFresh,tree,updated,run,actual,destId,
    ⟨returnPacket,packetId⟩,⟨sourcePacket⟩,prefixFrame,prefixTrace,shape⟩ := ready different
  have sourceRun := S05WildcardEntryBridge.invoke_positive address len reference
    input.contract.runtime.toState input.contract.resources ({} : FrameState)
  obtain ⟨otherOutput,created,_tag,_frame,_completed,_constructed,_runtime,capacity,growth,
    _child,_lookup,_roots,_positive,_activity⟩ := sourceRun
  have sameOutput : otherOutput = output := Except.ok.inj (created.symm.trans run)
  subst otherOutput
  have member : (reference.id,reference.entry) ∈ before.memory.live.toList :=
    Array.mem_toList_iff.mpr (Array.mem_of_find?_eq_some reference.live)
  have treeLength : reference.entry.allocation.extra.locations.size = reference.entry.allocation.byteSize :=
    input.contract.runtime.treeLength (reference.id,reference.entry) member
  have sourceCapacity : sourcePacket.entry.allocation.extra.locations.size = sourcePacket.entry.allocation.byteSize := by
    rw [sourcePacket.entryEq]
    exact capacity.trans treeLength
  have sourceBounds : reference.offset.toNat+len.toNat ≤ sourcePacket.entry.allocation.byteSize.bytes.toNat := by
    rw [sourcePacket.entryEq]
    change reference.offset.toNat+len.toNat ≤ reference.entry.allocation.byteSize.bytes.toNat
    rw [reference.size]
    exact reference.storage.bounds
  have nodeRoom : sourcePacket.entry.allocation.extra.nodes.size+2 < 65536 := by
    rw [sourcePacket.entryEq]
    change output.child.tree.nodes.size+2 < 65536
    have margin := input.contract.resources.nodeRoom (reference.id,reference.entry) member
    change reference.entry.allocation.extra.nodes.size+16 < 65536 at margin
    change output.child.tree.nodes.size ≤ reference.entry.allocation.extra.nodes.size+1 at growth
    omega
  have trackerEq : sourcePacket.tracker.global =
      (TypedBorrowSteps.registeredGlobal
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag) := by
    have registered : (S04ProtectUninit.finished
      (GeneralBorrowRawWildcardWindowFunctionScope.resultMachine (RawRootInvocation.machine #[] before)
        reference.tracker firstFresh reference.id reference.entry output.child.tree)
      place destination #[]
      { (RootArgumentsTwo.result
          (PositiveRootArguments.firstDone
            (RawRootInvocation.root before place input.contract.model.noDataRace)
            (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
              (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
                (Size.ofBytes address)) len ActualReferenceMetadata.reference).imm
            ({} : FrameState) reference.id reference.tracker.global.nextPointerTag) count).frame
        with location := .unwinding ⟨601⟩ }
      (({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag)
      secondFresh tree updated).machine.borrowTracker =
      some (TypedBorrowSteps.registeredTracker
        (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
        destination.tracker.global.nextPointerTag) := rfl
    exact congrArg MachineHooks.BorrowState.global
      (Option.some.inj (sourcePacket.enabled.symm.trans registered))
  have tagMargin := S02WildcardSharedTagMargin.after_second_protector input reference output
    firstFresh destination secondFresh
  let raw : GeneralBorrowRawShared.Input sourcePacket.entry.allocation.extra sourcePacket.tracker.global := {
    parentTag := reference.tracker.global.nextPointerTag
    parent := sourcePacket.child
    selected := sourcePacket.child
    maximum := some reference.tracker.global.nextPointerTag
    offset := reference.offset
    len := len
    tagged := sourcePacket.tagged
    positive := Classical.choice (GeneralBorrowReadRowRange.of_positive
      sourcePacket.entry.allocation.extra sourcePacket.tracker.global.protectedTags
      sourcePacket.child sourcePacket.child (some reference.tracker.global.nextPointerTag)
      reference.offset len sourcePacket.positive)
    distinct := sourcePacket.distinct
    order := by intro _ _; exact sourcePacket.order
    short := sourcePacket.short
    nodeRoom := by omega
    tagRoom := by rw [trackerEq]; exact tagMargin }
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
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let borrowFrame := owned.addProtector destination.id destination.tracker.global.nextPointerTag
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id
    destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  have frameTracked : installed.extra.borrowTracker = some borrowFrame := rfl
  exact ⟨output,firstFresh,destination,secondFresh,tree,updated,
    installed,after.machine,sourcePacket.entry,sourcePacket.tracker,raw,borrowFrame,
    returnPacket,sourcePacket,actual,rfl,rfl,rfl,rfl,destId,rfl,packetId,rfl,rfl,rfl,rfl,rfl,
    frameTracked,sourcePacket.enabled,sourcePacket.live,rfl,rfl,rfl,
    sourceCapacity,sourceBounds,nodeRoom,by rw [trackerEq]; exact tagMargin,
    prefixFrame,prefixTrace,shape⟩

end
end DuplicatePrefix.S02WildcardSourceWildcardSharedPrefixExact

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardSourceWildcardSharedPrefixExact.ready) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved wildcard/wildcard shared-ready dependency {dependency}"
