import duplicate_prefix.GeneralBorrowForestArgumentCopy
import duplicate_prefix.RootArgumentEntry
import duplicate_prefix.MetadataArgument
namespace DuplicatePrefix.GeneralBorrowForestFunctionEntryArgument
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess RootArgumentEntry
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem reference_storage_trivial : CompilerStorage.veryTriviallySized
    PreparedReflection.actual.compiler.runtime 3 = .ok true := by decide +kernel

theorem pass_argument
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (data : GeneralBorrowForestEntryValidity.Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (valid : (1 : MIR.LocalId) < frame.locals.size)
    (body : frame.body = RootBody.reflected.body.body)
    (dead : frame.locals[1].value = .dead)
    (cached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
 :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let liveFrame := RootArgumentEntry.liveFrame frame 1 valid
    let copied := GeneralBorrowForestArgumentCopy.copiedFrame liveFrame 1 value (by simpa only [liveFrame,RootArgumentEntry.liveFrame,Array.size_set] using valid)
    let finalTree := GeneralBorrowForestArgumentCopy.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    Call.passArgument (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩)
      (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret)
      (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret) 0 ⟨1,#[]⟩ 3 false
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame copied borrowFrame id tracker.global.nextPointerTag) with
          locals := copied.locals.set 1
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm),
             layout := (copied.locals[1]'(by simpa only [copied,GeneralBorrowForestArgumentCopy.copiedFrame,liveFrame,RootArgumentEntry.liveFrame,Array.size_set] using valid)).layout}
            (by simpa only [copied,GeneralBorrowForestArgumentCopy.copiedFrame,liveFrame,RootArgumentEntry.liveFrame,Array.size_set] using valid)} resultMachine) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let h := ExecutionMachine.callHooks cfg limits
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have typed : frame.body.locals[1]? = some 3 := by rw [body];rfl
  have storage := CallEntryLocals.storage_live options limits (remaining+1) span frames frame machine 1 3 valid
    typed reference_storage_trivial dead noClocks
  have postValid : (1 : MIR.LocalId) < (liveFrame frame 1 valid).locals.size := by simpa only [liveFrame,Array.size_set] using valid
  have postCached : ((liveFrame frame 1 valid).locals[1]'postValid).layout = some ActualReferenceMetadata.reference := by
    simpa only [liveFrame,Array.getElem_set_self] using cached
  have evaluate := CallEntryLocals.destination_cached options limits (remaining+1) span debugOff frames
    (liveFrame frame 1 valid) machine 1 ActualReferenceMetadata.reference postValid postCached ActualReferenceMetadata.reference_sized
  have compat : h.checkArgumentCompat () (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret)
      (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret)
      (Storage.withCurrent frames frame machine) = .ok true (Storage.withCurrent frames frame machine) := by
    change cfg.calls.compiler.checkArgumentCompat () _ _ _ = _
    rw [fields.callCompiler]
    exact CallEntryFacts.root_slice_argument_compat _ options.compatibilityBudget _
  apply CallArgumentStages.copy_argument h () _ _ _ 0 ⟨1,#[]⟩ 3 _ _ _ _ _
  · change (3 == (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret).layout.ty) = true
    with_unfolding_all rfl
  · change (ActualReferenceMetadata.reference.layout == (RootCompilerFacts.rootAbi.args.getD 0 RootCompilerFacts.rootAbi.ret).layout.layout) = true
    with_unfolding_all rfl
  · exact compat
  · rfl
  · rfl
  · exact storage
  · exact evaluate
  · exact GeneralBorrowForestArgumentCopy.copy_argument options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
      id entry base offset len parentTag positive nonzero signedFits bounds frames
      (liveFrame frame 1 valid) machine tracker enabled mode borrowFrame frameBorrow fresh data capacity 1 postValid .uninit
      (by simp [liveFrame,Array.getElem_set_self]) postCached noClocks ghost shallow cachedAddress present race metadata notConstructed _ rfl

#print axioms pass_argument
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``pass_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved generic root passArgument dependency {dependency}"
end
end DuplicatePrefix.GeneralBorrowForestFunctionEntryArgument
