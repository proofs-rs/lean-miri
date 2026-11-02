import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedEntryRaw
import duplicate_prefix.LenArgumentCopy
import duplicate_prefix.GeneralBorrowExposedScopedSharedArgumentCopy
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedArgumentRaw
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

abbrev copiedFrame := GeneralBorrowExposedScopedSharedArgumentCopy.copiedFrame
abbrev finalTree := GeneralBorrowExposedScopedSharedArgumentCopy.finalTree

/-- Actual shared MIR argument copy with real protected FnEntry runtime validation on
a general multiple-root forest. Every borrow success is derived from the
initial writable leaf resources; physical/compiler/fuel premises stay explicit. -/
theorem copy_argument
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
    (selected head : UniIndex) (tail : List UniIndex)
    (writable : Nat → Bool)
    (data : GeneralBorrowExposedScopedInactiveWritableSharedEntryRaw.Data entry.allocation.extra tracker.global.protectedTags
      parentTag tracker.global.nextPointerTag offset len selected head tail writable)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (old : Immediate Provenance)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some SharedReferenceMetadata.sharedLayout)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (view : RuntimeStackPlace Provenance)
    (destination : view.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size frame localId SharedReferenceMetadata.sharedLayout) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let copied := copiedFrame frame localId value valid
    let finalTree := GeneralBorrowExposedScopedInactiveWritableSharedArgumentRaw.finalTree entry.allocation.extra tracker parentTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate value,SharedReferenceMetadata.sharedLayout⟩ view (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        {(TypedBorrowSteps.registeredFrame copied borrowFrame id tracker.global.nextPointerTag) with
          locals := copied.locals.set localId
            {value := .live (.immediate (RetagReferencePlace.sliceValue cfg.access.runtime.base
              (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm),
             layout := (copied.locals[localId]'(by simpa only [copied,copiedFrame,GeneralBorrowExposedScopedSharedArgumentCopy.copiedFrame,Array.size_set] using valid)).layout}
            (by simpa only [copied,copiedFrame,GeneralBorrowExposedScopedSharedArgumentCopy.copiedFrame,Array.size_set] using valid)} resultMachine) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let copied := copiedFrame frame localId value valid
  have postValid : localId < copied.locals.size := by simpa only [copied,copiedFrame,GeneralBorrowExposedScopedSharedArgumentCopy.copiedFrame,Array.size_set] using valid
  have postLive : copied.locals[localId].value = .live (.immediate value) := by simp [copied,copiedFrame,GeneralBorrowExposedScopedSharedArgumentCopy.copiedFrame]
  have postCached : copied.locals[localId].layout = some SharedReferenceMetadata.sharedLayout := by
    simpa only [copied,copiedFrame,GeneralBorrowExposedScopedSharedArgumentCopy.copiedFrame,Array.getElem_set_self] using cached
  have checked := (GeneralBorrowExposedScopedInactiveWritableSharedEntryRaw.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    id entry base offset len parentTag positive nonzero signedFits bounds frames copied machine
    tracker enabled mode borrowFrame frameBorrow fresh selected head tail writable data capacity localId postValid postLive postCached ghost shallow
    cachedAddress present race metadata notConstructed)
  apply LenArgumentCopy.copy_with_nested_validation options limits remaining span debugOff frames frame machine
    localId old value valid live cached noClocks ghost shallow view destination _
  rw [validationEq]
  exact checked

#print axioms copy_argument
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``copy_argument) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved asmut argument dependency {dependency}"
end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedArgumentRaw
