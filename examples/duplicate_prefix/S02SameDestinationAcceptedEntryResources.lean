import duplicate_prefix.S02SameDestinationActivePacket
import duplicate_prefix.S02SameDestinationAcceptedEntryCurrentMargins
import duplicate_prefix.GeneralBorrowRawShared

namespace DuplicatePrefix.S02SameDestinationAcceptedEntryResources
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2500000
noncomputable section

/-- The exact same-allocation installed call has the complete raw shared
borrow input and source activity for the following MIR Ref. Node/tag margins
are derived after both real protected constructors from original resources. -/
theorem after_exact
    {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits}
    {remaining : Nat} {span : PreparedContracts.FixedSpanQuery} {before : Before} {place : MPlaceTy Provenance}
    (id : AllocId) (tag : BorTag) (address len count : UInt64)
    (input : S05ConsistentCallSpecification.ConsistentContract options limits remaining span before
      (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len place)
    (nonempty : len ≠ 0) (sameAllocation : id = input.contract.destination.id)
    (returnTag : BorTag) (returnConcrete : input.contract.destination.pointer.provenance = .concrete input.contract.destination.id returnTag) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (tracker : MachineHooks.BorrowState) (installed : CompilerFrameContext.ActualFrame)
      (post : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (child : UniIndex)
      (raw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),.Copy (EmptyRootArguments.second count)]
        false (.memory place) (.stop true) ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] installed post) ∧
      post.borrowTracker = some tracker ∧ post.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
      raw.parentTag = reference.tracker.global.nextPointerTag ∧ raw.parent = child ∧ raw.offset = reference.offset ∧ raw.len = len ∧
      DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra child .Write reference.offset (reference.offset+len) ∧
      sourceEntry.allocation.extra.nodes.size+4 < 65536 ∧ sourceEntry.allocation.extra.nodes.size+4 ≤ 4294967295 ∧
      tracker.global.nextPointerTag.value.toNat+3 < 18446744073709551615 ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra tracker.global.protectedTags
        (some raw.parent) (some raw.selected) raw.maximum raw.offset raw.len) ∧
      sourceEntry.allocation.extra.locations.size = sourceEntry.allocation.byteSize ∧
      sourceEntry.allocation.byteSize = reference.entry.allocation.byteSize ∧
      sourceEntry.allocation.len = reference.entry.allocation.len ∧ sourceEntry.allocation.mutability = .Mut ∧
      tracker.global.nextPointerTag.value.toNat = reference.tracker.global.nextPointerTag.value.toNat+2 := by
  obtain ⟨reference,firstFresh,destination,secondFresh,updated,sourceChild,returnChild,sourceRaw,sourceBefore,sourceNode,returnNode,returnParent,
      actual,sameId,destOffset,beforeTagged,beforePresent,beforeTag,beforeLeaf,beforeHidden,beforeActivity,
      sourceTagged,sourcePresent,sourceTag,sourceHidden,returnPresent,returnSame,returnLeaf,returnHidden,
      returnSource,returnEdge,differentChildren,rootsAfter,shortAfter,extra,bytes,length,mutable,post,postOrder,
      sourcePositive,returnTagged,returnPositive,returnActive,sourceActive⟩ :=
    S02SameDestinationActivePacket.enters id tag address len count input nonempty sameAllocation returnTag returnConcrete
  let current := GeneralBorrowRawFnEntryScope.resultMachine (RawRootInvocation.machine #[] before) reference.tracker firstFresh
    reference.id reference.entry tag reference.offset len
  let root := RawRootInvocation.root before place input.contract.model.noDataRace
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag) (Size.ofBytes (reference.base+reference.offset)))
    len ActualReferenceMetadata.reference).imm
  let frame := (RootArgumentsTwo.result (PositiveRootArguments.firstDone root adjusted ({} : FrameState)
    reference.id reference.tracker.global.nextPointerTag) count).frame
  let changed := {frame with location := .unwinding ⟨601⟩}
  let owned := ({} : FrameState).addProtector reference.id reference.tracker.global.nextPointerTag
  let tree := GeneralBorrowRawFnEntryArgument.finalTree destination.entry.allocation.extra destination.tracker returnTag destination.offset 1
  let after := S04ProtectUninit.finished current place destination #[] changed owned secondFresh tree updated
  let protectedFrame := TypedBorrowSteps.registeredFrame changed owned destination.id destination.tracker.global.nextPointerTag
  let installed := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
  let tracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker destination.tracker secondFresh)
    destination.tracker.global.nextPointerTag
  let sourceEntry := {destination.entry with allocation := updated}
  have tracked : after.machine.borrowTracker = some tracker := rfl
  have refTracker : reference.tracker = input.contract.tracker := Option.some.inj (reference.enabled.symm.trans input.contract.runtime.enabled)
  have destTracker : destination.tracker = ⟨TypedRetagGeneric.protectedGlobal reference.tracker.global firstFresh,reference.tracker.retagMode⟩ :=
    Option.some.inj destination.enabled.symm
  have firstValue : destination.tracker.global.nextPointerTag.value.toNat = reference.tracker.global.nextPointerTag.value.toNat+1 := by
    rw [destTracker]
    exact GenericFunctionEntryNumerics.successor_value reference.tracker.global.nextPointerTag firstFresh
  have secondValue : tracker.global.nextPointerTag.value.toNat = destination.tracker.global.nextPointerTag.value.toNat+1 :=
    GenericFunctionEntryNumerics.successor_value destination.tracker.global.nextPointerTag secondFresh
  have margin : reference.tracker.global.nextPointerTag.value.toNat+16 < 2^64 := by
    simpa only [←refTracker] using input.contract.resources.tagRoom
  have room : tracker.global.nextPointerTag.value < 18446744073709551615 := by
    apply UInt64.lt_iff_toNat_lt.mpr
    change tracker.global.nextPointerTag.value.toNat < 18446744073709551615
    rw [secondValue,firstValue]
    omega
  have referenceId : reference.id = id := by
    have binding := reference.binding
    simp only [DuplicatePrefixReferenceInput.Binding,Pointer.new] at binding
    exact binding.1.symm
  have concrete : destination.pointer.provenance = .concrete destination.id returnTag := by
    have physical := destination.physicalPointer.symm.trans input.contract.destination.physicalPointer
    have provenance := congrArg (fun ptr : Pointer (Option Provenance) => ptr.provenance) physical
    simp only [Pointer.withOptionalProvenance] at provenance
    have destId : destination.id = input.contract.destination.id := sameId.trans (referenceId.trans sameAllocation)
    rw [Option.some.inj provenance,destId]
    exact returnConcrete
  obtain ⟨_sourceChild,_sourceRaw,_sourceId,_parent,_offset,_len,sourceLive,_enabled,_runtime,_positive⟩ :=
    S02ConcreteSourceCurrent.source_ready_at_actual_current id tag address len input reference firstFresh
  have destEntryEq : destination.entry = {reference.entry with allocation := (reference.entry.allocation.setExtra
      (GeneralBorrowRawFnEntryArgument.finalTree reference.entry.allocation.extra reference.tracker tag reference.offset len))} := by
    have found := destination.live
    rw [sameId] at found
    exact congrArg Prod.snd (Option.some.inj (found.symm.trans sourceLive))
  have margins := S02SameDestinationAcceptedEntryCurrentMargins.current id tag address len input reference firstFresh destination sameId secondFresh returnTag concrete
  obtain ⟨sourcePositive⟩ := sourcePositive
  let raw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global := {
    parentTag := reference.tracker.global.nextPointerTag
    parent := sourceChild
    selected := sourceRaw.selected
    maximum := sourceRaw.maximum
    offset := reference.offset
    len := len
    tagged := by change updated.extra.indexOfTag _ = _;rw [extra];exact sourceTagged
    positive := by
      change GeneralBorrowReadRowRange.Positive updated.extra tracker.global.protectedTags sourceChild sourceRaw.selected sourceRaw.maximum reference.offset len
      rw [extra]
      exact Classical.choice (GeneralBorrowReadRowRange.of_positive _ _ _ _ _ _ _ sourcePositive)
    distinct := by change updated.extra.roots.toList.Nodup;rw [extra];exact rootsAfter
    order := by intro _ _;change GeneralBorrowWildcardParentTagOrder.ParentTagOrder updated.extra;rw [extra];exact postOrder
    short := by change updated.extra.nodes.size < 65536;rw [extra];exact shortAfter
    nodeRoom := by change updated.extra.nodes.size+1 ≤ 4294967295;rw [extra];omega
    tagRoom := room }
  refine ⟨reference,tracker,installed,after.machine,sourceEntry,sourceChild,raw,actual,tracked,?_,rfl,rfl,rfl,rfl,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [←sameId]
    exact MemoryCopyBridge.live_lookup_replaced _ _ _
  · change DuplicatePrefixBorrowContract.RuntimeFacts updated.extra tracker.global
    rw [extra]
    exact post
  · change GeneralBorrowFreshActiveWithin.ActiveWithin updated.extra sourceChild .Write reference.offset (reference.offset+len)
    rw [extra]
    exact sourceActive
  · change updated.extra.nodes.size+4 < 65536
    rw [extra]
    exact margins.1
  · change updated.extra.nodes.size+4 ≤ 4294967295
    rw [extra]
    exact margins.2.1
  · exact margins.2.2.1
  · change Nonempty (DuplicatePrefixBorrowAuthorization.Positive updated.extra tracker.global.protectedTags
      (some sourceChild) (some sourceRaw.selected) sourceRaw.maximum reference.offset len)
    rw [extra]
    exact ⟨sourcePositive⟩
  · change updated.extra.locations.size = updated.byteSize
    rw [extra,bytes]
    exact margins.2.2.2

  · change updated.byteSize = reference.entry.allocation.byteSize
    rw [bytes,destEntryEq];rfl
  · change updated.len = reference.entry.allocation.len
    rw [length,destEntryEq];rfl
  · exact mutable
  · omega

end
end DuplicatePrefix.S02SameDestinationAcceptedEntryResources

open Lean Elab Command in
run_cmd do
  for ax in (← collectAxioms ``DuplicatePrefix.S02SameDestinationAcceptedEntryResources.after_exact) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains ax do
      throwError "unapproved axiom {ax}"
