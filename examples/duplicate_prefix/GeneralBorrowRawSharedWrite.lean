import duplicate_prefix.GeneralBorrowRawSharedExpression
namespace DuplicatePrefix.GeneralBorrowRawSharedWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo
open RootReferenceWrite (written)
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Actual unprotected shared .Default validation/write from initial raw Read data.
The fixed MIR shared Ref statement is proved separately by RawDefaultExpression. -/
theorem positive_cached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (currentMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (old : Immediate Provenance) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some (layout true))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (raw : GeneralBorrowRawShared.Input entry.allocation.extra tracker.global)
    (rawTag : raw.parentTag = parentTag) (rawOffset : raw.offset = offset) (rawLen : raw.len = len)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let finalTree := (GeneralBorrowRawSharedExpression.child entry.allocation.extra tracker.global.protectedTags
      parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
    let cfg := config options remaining span
    let value := RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len (layout true)
    let output := RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).writeImmediate
      () value.imm (LocalPlaces.localRuntimePlace frames.size frame localId (layout true))
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (written frame localId output.imm valid) resultMachine) := by
  let parentTree := (GeneralBorrowRawSharedExpression.read entry.allocation.extra tracker.global.protectedTags parentTag offset len .VisitChildrenOfAccessed).tree
  let finalTree := (GeneralBorrowRawSharedExpression.child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
  have run := GeneralBorrowRawShared.literal entry.allocation.extra tracker.global runtime raw
  simp only [rawTag,rawOffset,rawLen] at run
  have readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset) (Size.ofBytes len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentTree := rfl
  have readDone := run.1
  have child : parentTree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) (initial true)) (policy true).outsidePermission false = ⟨finalTree,.ok ()⟩ := by
    have done := run.2.1
    change (GeneralBorrowRawSharedExpression.child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).outcome = .ok () at done
    change GeneralBorrowRawSharedExpression.child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed = ⟨(GeneralBorrowRawSharedExpression.child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree,.ok ()⟩
    cases equation : GeneralBorrowRawSharedExpression.child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed with
    | mk tree result => simp only [equation] at done;cases done;rfl
  let cfg := config options remaining span
  let value := RetagReferencePlace.sliceValue cfg.access.runtime.base
    (Pointer.new (Provenance.concrete id parentTag) (Size.ofBytes (base+offset))) len (layout true)
  let post := written frame localId value.imm valid
  have postValid : localId < post.locals.size := by simpa [post,written] using valid
  have postLive : post.locals[localId].value = .live (.immediate value.imm) := by simp [post,written]
  have postCached : post.locals[localId].layout = some (layout true) := by simpa [post,written] using cached
  have info := RootReferenceInfo.facts options remaining span ctx true
  have validator := RootReferenceValidator.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    (layout true) (mutability true) .Default (policy true) (initial true) info.protection info.associated info.initialState
    (by decide) info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference info.sized info.readable
    (name true) info.named info.classified id entry base offset len parentTag positive nonzero signedFits bounds
    frames post machine tracker enabled currentMode fresh localId postValid postLive postCached ghost shallow
    cachedAddress present race parentTree finalTree readTree readDone child metadata notConstructed
  have finalFrame (newValue : Immediate Provenance) : written post localId newValue postValid = written frame localId newValue valid := by
    simp [post,written,Array.set_set]
  apply RootReferenceWrite.of_validation options limits remaining span debugOff validityFuel validationFuel frames frame machine
    localId old value.imm (layout true) valid live cached info.sized noClocks ghost shallow
  simpa only [post,value,written,Array.getElem_set_self,Array.set_set] using validator

end
end DuplicatePrefix.GeneralBorrowRawSharedWrite
