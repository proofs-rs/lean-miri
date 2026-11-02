import duplicate_prefix.GeneralBorrowForestAsMutInstall
import duplicate_prefix.ScopedFrame
namespace DuplicatePrefix.GeneralBorrowForestAsMutScopedInstall
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem install
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
    (defaultMode : tracker.retagMode = .Default)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (data : GeneralBorrowForestEntryValidity.Data entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (valid : (1 : MIR.LocalId) < frame.locals.size)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (dead : frame.locals[1].value = .dead)
    (uncached : frame.locals[1].layout = none)
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
    let finalTree := GeneralBorrowForestArgumentCopy.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (GeneralBorrowForestAsMutInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value)
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (GeneralBorrowForestAsMutInstall.resultFrame frame valid value
          (RetagReferencePlace.sliceValue cfg.access.runtime.base
            (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
          borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let h := ExecutionMachine.callHooks cfg limits
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let enteredTracker := {tracker with retagMode := RetagPolicy.RetagMode.FnEntry}
  let enteredMachine := ScopedFrame.entered machine tracker .FnEntry
  let finalTree := GeneralBorrowForestArgumentCopy.finalTree entry.allocation.extra tracker parentTag offset len
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine enteredMachine enteredTracker fresh)
      (ReferenceBorrowDriver.allocatedTracker enteredTracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  let resultFrame := GeneralBorrowForestAsMutInstall.resultFrame frame valid value adjusted borrowFrame id tracker.global.nextPointerTag
  let nextTracker := TypedBorrowSteps.registeredTracker (ReferenceBorrowDriver.allocatedTracker enteredTracker fresh) tracker.global.nextPointerTag
  have installed := GeneralBorrowForestAsMutInstall.install options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len parentTag positive nonzero signedFits bounds frames frame
    enteredMachine enteredTracker rfl rfl borrowFrame frameBorrow fresh data capacity valid body identity callee dead uncached
    noClocks ghost shallow cachedAddress present race metadata notConstructed
  have body : GeneralBorrowForestAsMutInstall.action h value
      {(Storage.withCurrent frames frame machine) with machine := ScopedFrame.entered machine tracker .FnEntry} =
      .ok (1,1) (Storage.withCurrent frames resultFrame resultMachine) := installed
  have scope := ScopedFrame.changed_state (GeneralBorrowForestAsMutInstall.action h value) (Storage.withCurrent frames frame machine)
    (Storage.withCurrent frames resultFrame resultMachine) tracker nextTracker .FnEntry (1,1) enabled rfl body
  change MachineHooks.withRetagMode .FnEntry (GeneralBorrowForestAsMutInstall.action h value) (Storage.withCurrent frames frame machine) = _
  simpa only [Storage.withCurrent,resultMachine,resultFrame,nextTracker,enteredMachine,enteredTracker,
    ScopedFrame.entered,TypedBorrowSteps.registeredMachine,TypedBorrowSteps.registeredTracker,
    TypedBorrowSteps.registeredGlobal,ReferenceBorrowDriver.allocatedMachine,ReferenceBorrowDriver.allocatedTracker] using scope

#print axioms install
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``install) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved scoped asmut dependency {dependency}"
end
end DuplicatePrefix.GeneralBorrowForestAsMutScopedInstall
