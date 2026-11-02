import duplicate_prefix.GeneralBorrowFreshRootScopedSharedExpression
import duplicate_prefix.GeneralBorrowFreshRootScopedSharedNext
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedSharedStatement
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo RootReferenceTrees GeneralBorrowFreshRootScopedSharedExpression
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
theorem step_resources
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
    (parentTag : BorTag)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (raw : GeneralBorrowFreshRootScopedShared.Input entry.allocation.extra tracker.global)
    (rawTag : raw.parentTag = parentTag) (rawOffset : raw.offset = offset) (rawLen : raw.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (validSource : (1 : MIR.LocalId) < frame.locals.size) (validDest : (RootReferenceFacts.destination true) < frame.locals.size)
    (sourceLive : frame.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (sourceCached : frame.locals[1].layout = some ActualReferenceMetadata.reference)
    (destLive : frame.locals[RootReferenceFacts.destination true].value = .live (.immediate .uninit))
    (destUncached : frame.locals[RootReferenceFacts.destination true].layout = none)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false)
    (shortRoom : entry.allocation.extra.nodes.size+1 < 65536)
    (nodeRoom : entry.allocation.extra.nodes.size+2 ≤ 4294967295)
    (tagRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615) :
    let inner := config options remaining span
    let value := RetagReferencePlace.sliceValue inner.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout true)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry (child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree}
    (ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent frames frame machine) =
      (Storage.withCurrent frames (CopyHelperSteps.advance
        (ActualLocalCopy.written frame (RootReferenceFacts.destination true) (layout true) validDest value.imm)
        (RootReferenceFacts.location true)) resultMachine,.ok true)) ∧
    let finalTree := (GeneralBorrowFreshRootScopedSharedExpression.child entry.allocation.extra tracker.global.protectedTags parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
    DuplicatePrefixBorrowContract.RuntimeFacts finalTree (ReferenceBorrowDriver.allocatedTracker tracker fresh).global ∧
    finalTree.locations.size = entry.allocation.extra.locations.size ∧
    ∃ next : GeneralBorrowFreshRootScopedSharedFnEntry.Input finalTree (ReferenceBorrowDriver.allocatedTracker tracker fresh).global,
      next.parentTag = tracker.global.nextPointerTag ∧ next.selected = raw.selected ∧ next.maximum = raw.maximum ∧
      next.offset = offset ∧ next.len = len := by
  have statement := GeneralBorrowFreshRootScopedSharedExpression.positive_statement options limits remaining span preciseOff implicitOff debugOff cmp
    dynamicFuel validityFuel fuelEq validationFuel base offset len id entry positive nonzero signedFits frames frame machine
    sourceBody identity callee located tracker enabled defaultMode fresh parentTag runtime raw rawTag rawOffset rawLen capacity
    validSource validDest sourceLive sourceCached destLive destUncached noClocks ghost shallow cachedAddress present race metadata notConstructed
  subst parentTag
  subst offset
  subst len
  refine ⟨statement,?_⟩
  exact GeneralBorrowFreshRootScopedSharedNext.next_input entry.allocation.extra tracker runtime raw shortRoom nodeRoom tagRoom

end
end DuplicatePrefix.GeneralBorrowFreshRootScopedSharedStatement
