import duplicate_prefix.GeneralBorrowRawMutableTargetActivity
import duplicate_prefix.GeneralBorrowRawDefaultCopyLedger
namespace DuplicatePrefix.GeneralBorrowRawDefaultCopyActivity
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
/-- Actual accepted mutable suffix carries arbitrary original ROOT activity
from phase-entry data through both real constructors and release. -/
theorem invoke
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (parentTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808) (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (caller : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts entry.allocation.extra tracker.global)
    (raw : GeneralBorrowRawDefault.Input entry.allocation.extra tracker.global)
    (rawTag : raw.parentTag = parentTag) (rawOffset : raw.offset = offset) (rawLen : raw.len = len)
    (capacity : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (destValid : 15 < caller.locals.size)
    (destLive : caller.locals[15].value = .live (.immediate .uninit))
    (uncached : caller.locals[15].layout = none)
    (callerClocks : caller.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent #[] caller machine)).entries.any (·.value.ty == 4) = false)
    (thread : Miri.Concurrency.ThreadRecord)
    (active : machine.threads.activeThread? = some thread)
    (headroom : entry.allocation.extra.nodes.size+2 < 65536)
    (tagsRoom : tracker.global.nextPointerTag.value.toNat+1 < 18446744073709551615)
    (preciseOff : options.retag.preciseInteriorMut = false)
    (implicitOff : options.retag.implicitWrites = false)
    (source : PreparedContracts.SourceComparator) (budget : Nat) (dispatch : limits.callDispatch = budget+1)
    (backend : machine.user.payload.payload.user.backend = .none)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true)
    (threadTop : thread.topUserRelevantFrame = some 0)
    (size : caller.locals.size = 25)
    (callerBody : caller.body = RootBody.reflected.body.body)
    (identity : caller.bodyIdentity = RootBody.reflected.body.identity)
    (callee : caller.functionInstance = RootBody.reflected.functionInstance)
    (track : caller.trackCallerArg = none) (relevant : caller.extra.userRelevance > 0)
    (immediate : CopyHelperCleanup.AllImmediate caller)
    (located : caller.location = .mir ⟨6,7⟩)
    (valid16 : 16 < caller.locals.size)
    (dead16 : caller.locals[16].value = .live (.immediate .uninit))
    (uncached16 : caller.locals[16].layout = none)
    (valid1 : 1 < caller.locals.size)
    (source1 : caller.locals[1].value = .live (.immediate (RetagReferencePlace.sliceValue
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm))
    (cached1 : caller.locals[1].layout = some ActualReferenceMetadata.reference)
    (count : UInt64) (countPositive : (0 : UInt64) < count) (within : count ≤ len/2)
    (slot2 : caller.locals[2]? = some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩)
    (slot13 : caller.locals[13]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩)
    (unused : ∀ index, 17 ≤ index → index ≤ 24 → caller.locals[index]? = some ⟨.dead,none⟩)
    (target : UniIndex)
    (oldActivity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write offset (offset+len)) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ packet : GeneralBorrowRawAsMutToCopy.Input, ∃ result finalMachine,
      SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] caller machine)
        (Storage.withCurrent #[] result finalMachine) ∧
      packet.tag = (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag ∧ packet.count = count ∧
      PositiveRootSuccessProfile.FrameShape packet.caller result (GeneralBorrowRawAsMutToCopy.pointer packet)
        (Scalar.fromPointer cfg.access.runtime.base
          (Pointer.new (.concrete id packet.tag) (Size.ofBytes (base+offset+count)))) count ∧
      finalMachine.memory = GeneralBorrowRawAsMutToCopy.memory packet ∧
      finalMachine.borrowTracker = some (GeneralBorrowRawAsMutToCopy.held packet) ∧
      DuplicatePrefixBorrowContract.RuntimeFacts
        (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
        (GeneralBorrowRawAsMutToCopy.held packet).global ∧
      Nonempty (DuplicatePrefixBorrowAuthorization.Positive
        (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
        (GeneralBorrowRawAsMutToCopy.held packet).global.protectedTags
        (some packet.anchor) (some packet.selected) packet.maximum packet.offset packet.len) ∧
      (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree.indexOfTag packet.tag = some packet.anchor ∧
      GeneralBorrowRawAsMutCopyLedger.Metadata entry machine id base offset len count packet ∧
      GeneralBorrowRawAsMutCopyLedger.Outcome packet finalMachine ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin
        (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
        target .Write offset (offset+len) ∧
      ∃ secondFresh : (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag.value < 18446744073709551615,
        GeneralBorrowRawAsMutCopyLedger.Resources
          (GeneralBorrowRawFnEntryArgument.finalTree
            (GeneralBorrowRawDefaultExpression.child entry.allocation.extra tracker.global.protectedTags
              parentTag tracker.global.nextPointerTag offset len .VisitChildrenOfAccessed).tree
            (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag offset len)
          (TypedBorrowSteps.registeredTracker
            (ReferenceBorrowDriver.allocatedTracker (ReferenceBorrowDriver.allocatedTracker tracker fresh) secondFresh)
            (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag)
          (ReferenceBorrowDriver.allocatedTracker tracker fresh).global.nextPointerTag packet ∧
          GeneralBorrowRawAsMutCopyLedger.Configuration options limits remaining span validityFuel packet := by
  obtain ⟨packet,result,finalMachine,trace,packetTag,packetCount,shape,memory,tracked,postRuntime,postPositive,postTagged,metadataLedger,outcome,secondFresh,resources,configuration⟩ :=
    GeneralBorrowRawDefaultCopyLedger.invoke options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq id entry base offset len parentTag positive nonzero signedFits bounds caller machine tracker enabled defaultMode fresh runtime raw rawTag rawOffset rawLen capacity destValid destLive uncached callerClocks ghost shallow cachedAddress present race metadata notConstructed thread active headroom tagsRoom preciseOff implicitOff source budget dispatch backend unchecked noGc fixed threadTop size callerBody identity callee track relevant immediate located valid16 dead16 uncached16 valid1 source1 cached1 count countPositive within slot2 slot13 unused
  have initialActivity : GeneralBorrowFreshActiveWithin.ActiveWithin entry.allocation.extra target .Write
      raw.offset (raw.offset+raw.len) := by rw [rawOffset,rawLen];exact oldActivity
  have literal := GeneralBorrowRawMutableTargetActivity.suffix entry.allocation.extra tracker runtime raw
    headroom tagsRoom target initialActivity
  simp only [rawTag,rawOffset,rawLen] at literal
  have finalActivity : GeneralBorrowFreshActiveWithin.ActiveWithin
      (packet.entry.allocation.extra.releaseProtector packet.tag packet.tracker.global.protectedTags).tree
      target .Write offset (offset+len) := by
    rw [resources.treeEq,resources.tagEq,resources.trackerEq]
    exact literal.2.2
  exact ⟨packet,result,finalMachine,trace,packetTag,packetCount,shape,memory,tracked,postRuntime,postPositive,postTagged,
    metadataLedger,outcome,finalActivity,secondFresh,resources,configuration⟩
end
end DuplicatePrefix.GeneralBorrowRawDefaultCopyActivity
