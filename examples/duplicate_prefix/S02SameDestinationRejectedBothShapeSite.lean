import duplicate_prefix.S02SeparateDestinationSharedFrame
import duplicate_prefix.S02SameDestinationSharedResources
import duplicate_prefix.S02SameDestinationRejectedEntryPrefix
import duplicate_prefix.S02SameDestinationInstalledFrame
import duplicate_prefix.S02ConcreteReferenceIdentity

namespace DuplicatePrefix.S02SameDestinationRejectedBothShapeSite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixCallSpecification CanonicalConfigFacts ActualReferenceContext
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
noncomputable section

/-- The actual positive call and pure prefix arrive at the shared-Ref site
with the source pointer matching the very same current source borrow packet.
Independent existential proofs are aligned by deterministic call results. -/
theorem actual_rejected_both_shape_site
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
    (rejected : count > len/2) :
    ∃ (reference : DuplicatePrefixReferenceInput.Positive before
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) len)
      (tracker : MachineHooks.BorrowState)
      (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
      (child : UniIndex) (raw : GeneralBorrowRawShared.Input sourceEntry.allocation.extra tracker.global)
      (entry frame : CompilerFrameContext.ActualFrame)
      (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser),
      Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
        RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
        #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base
          (.pointer (Pointer.new (.concrete id tag) (Size.ofBytes address))) len),
          .Copy (EmptyRootArguments.second count)] false (.memory place) (.stop true)
        ⟨⟨#[]⟩,before⟩ = .ok () (Storage.withCurrent #[] entry machine) ∧
      SuccessfulTrace.Trace (config options (remaining+1) span) limits
        (Storage.withCurrent #[] entry machine)
        (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span machine)) ∧
      GenericFunctionEntryPrefix.Shape entry frame count ∧
      frame.body = RootBody.reflected.body.body ∧
      frame.bodyIdentity = RootBody.reflected.body.identity ∧
      frame.functionInstance = RootBody.reflected.functionInstance ∧
      frame.location = .mir ⟨2,11⟩ ∧ frame.locals.size = 25 ∧
      frame.extra.dataRace = none ∧
      frame.locals[1]? = some ⟨.live (.immediate
        (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
          (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
            (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm),
        some ActualReferenceMetadata.reference⟩ ∧
      frame.locals[11]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      frame.locals[12]? = some ⟨.live (.immediate .uninit),none⟩ ∧
      CopyHelperCleanup.AllImmediate frame ∧
      machine.borrowTracker = some tracker ∧
      machine.memory.live.find? (fun row => row.1 == reference.id) = some (reference.id,sourceEntry) ∧
      raw.parentTag = reference.tracker.global.nextPointerTag ∧
      raw.parent = child ∧ raw.offset = reference.offset ∧ raw.len = len ∧
      DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra
        tracker.global.protectedTags (some child) (some raw.selected) raw.maximum reference.offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra child .Write
        reference.offset (reference.offset+len) := by
  obtain ⟨reference,tracker,installed,post,sourceEntry,child,raw,actual,tracked,live,
    rawTag,rawParent,rawOffset,rawLen,runtime,activity,shortRoom,nodeRoom,tagRoom,⟨bothRaw⟩,_capacity⟩ :=
    S02SameDestinationSharedResources.after_exact id tag address len count input nonempty sameAllocation
      returnTag returnConcrete
  have both : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra tracker.global.protectedTags
      (some child) (some raw.selected) raw.maximum reference.offset len := by
    simpa only [rawParent,rawOffset,rawLen] using bothRaw
  obtain ⟨entry,frame,machine,actual2,trace,shape⟩ :=
    S02SameDestinationRejectedEntryPrefix.actual_nonzero_prefix id tag address len count input nonempty
      sameAllocation returnTag returnConcrete rejected
  obtain ⟨reference2,destId,destTag,entry2,machine2,actual3,installedEq,_body,_identity,_callee,
    _location,_size,_slot1,_slot2,_metadata,_notConstructed,_thread⟩ :=
    S02SameDestinationInstalledFrame.concrete_positive_installed id tag address len count input nonempty
      sameAllocation returnTag returnConcrete
  have same : Storage.withCurrent #[] installed post = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (actual.symm.trans actual2)).2
  have same2 : Storage.withCurrent #[] entry2 machine2 = Storage.withCurrent #[] entry machine :=
    (EStateM.Result.ok.inj (actual3.symm.trans actual2)).2
  have frameEq : entry2 = entry := by
    have h := congrArg (fun s : RootState => s.stack.frames[0]?) same2
    exact Option.some.inj (by simpa [Storage.withCurrent] using h)
  have physical := S02ConcreteReferenceIdentity.current_pointer_same before id tag address len reference2 reference
  have sourceValue :
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference2.id reference2.tracker.global.nextPointerTag)
          (Size.ofBytes (reference2.base+reference2.offset))) len ActualReferenceMetadata.reference).imm =
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm := by
    rw [physical]
  have currentShape : GenericFunctionEntryPrefix.Shape entry2 frame count := by
    rw [frameEq]
    exact shape
  have site := S02SeparateDestinationSharedFrame.of_shape options remaining span before place
    input.contract.model.noDataRace id tag address len reference2 count destId destTag entry2 frame
    installedEq currentShape
  obtain ⟨body,identity,callee,located,size,clocks,source,slot11,slot12,immediate⟩ := site
  have actualSource : frame.locals[1]? = some ⟨.live (.immediate
      (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
        (Pointer.new (.concrete reference.id reference.tracker.global.nextPointerTag)
          (Size.ofBytes (reference.base+reference.offset))) len ActualReferenceMetadata.reference).imm),
      some ActualReferenceMetadata.reference⟩ := by
    rw [sourceValue] at source
    exact source
  have entryEq : installed = entry := by
    have h := congrArg (fun s : RootState => s.stack.frames[0]?) same
    exact Option.some.inj (by simpa [Storage.withCurrent] using h)
  have machineEq : post = machine := congrArg (fun s : RootState => s.machine) same
  have installedTrace : SuccessfulTrace.Trace (config options (remaining+1) span) limits
      (Storage.withCurrent #[] installed post)
      (Storage.withCurrent #[] frame (RootZeroCompleteState.tick options remaining span post)) := by
    rw [entryEq,machineEq]
    exact trace
  have installedShape : GenericFunctionEntryPrefix.Shape installed frame count := by
    rw [entryEq,←frameEq]
    exact currentShape
  exact ⟨reference,tracker,sourceEntry,child,raw,installed,frame,post,actual,installedTrace,
    installedShape,body,identity,callee,located,size,clocks,actualSource,slot11,slot12,immediate,
    tracked,live,rawTag,rawParent,rawOffset,rawLen,runtime,⟨both⟩,activity⟩

end
end DuplicatePrefix.S02SameDestinationRejectedBothShapeSite

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02SameDestinationRejectedBothShapeSite.actual_rejected_both_shape_site) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved separate shared-site dependency {dependency}"
