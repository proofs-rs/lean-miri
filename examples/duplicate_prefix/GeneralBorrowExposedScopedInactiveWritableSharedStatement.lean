import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedExpression
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedData
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedStatement
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo RootReferenceTrees
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- The actual physical MIR shared-expression step from initial exposed-leaf
resources. Scoped Read permissions and constructor inputs are formed internally. -/
theorem executes {profileMode : ProfileMode}
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (base offset len : UInt64)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (located : frame.location = .mir (RootReferenceFacts.location true))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (input : GeneralBorrowFreshMetadataChildShared.Input)
    (selected head : UniIndex) (tail : List UniIndex) (writable : Nat → Bool)
    (raw : GeneralBorrowExposedScopedInactiveWritableSharedConstructor.ResourcesFor input tracker.global.protectedTags selected head tail writable profileMode)
    (treeEq : input.tree = entry.allocation.extra)
    (tagEq : input.newTag = tracker.global.nextPointerTag)
    (offsetEq : input.offset = offset) (lenEq : input.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination true) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id input.parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination true].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (GeneralBorrowForestMixedShared.child entry.allocation.extra tracker.global.protectedTags input.parentTag tracker.global.nextPointerTag false offset len .VisitChildrenOfAccessed).tree}
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (CopyHelperSteps.advance
        (ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) validDest value.imm)
        (RootReferenceFacts.location true)) resultMachine,.ok true) := by
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedInactiveWritableSharedData.build input tracker.global.protectedTags selected head tail writable raw
  have baseOwned : GeneralRangeMapOrigins.OwnedOn
      (fun location=>Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data input.tree location tracker.global.protectedTags
        input.parent selected head tail raw.component.support writable)) input.offset (input.offset+input.len) input.tree.locations := by
    intro position valid positive lower upper
    obtain ⟨data⟩:=owned position valid positive lower upper
    exact ⟨data⟩
  rw [treeEq] at context
  have owned' : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data entry.allocation.extra location tracker.global.protectedTags
        input.parent selected head tail raw.component.support writable)) offset (offset+len) entry.allocation.extra.locations := by
    simpa only [treeEq,offsetEq,lenEq] using baseOwned
  have covered := input.covered
  have tagPresent := input.parentTagPresent
  have tagFresh := input.fresh
  have noFree := input.noFree
  have aligned := input.aligned
  have fits := input.fits
  have well := input.well
  have bounds := input.bounds
  have forest := raw.forest
  rw [treeEq] at covered tagPresent noFree aligned fits well forest
  rw [treeEq,tagEq] at tagFresh
  rw [treeEq,offsetEq,lenEq] at bounds
  exact GeneralBorrowExposedScopedInactiveWritableSharedExpression.positive_statement options limits remaining span preciseOff implicitOff debugOff cmp
    dynamicFuel validityFuel fuelEq validationFuel base offset len id entry positive nonzero signedFits frames frame machine
    sourceBody identity callee located tracker enabled defaultMode fresh input.parentTag input.parent selected head tail
    context covered tagPresent tagFresh forest noFree aligned fits raw.component.support well bounds writable capacity owned'
    validSource validDest sourceLive sourceCached destLive destUncached noClocks ghost shallow cachedAddress present race metadata notConstructed
end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableSharedStatement
