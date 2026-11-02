import duplicate_prefix.LenInstall
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedArgumentRaw
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableSharedArgumentCopy
namespace DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableLenInstall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem install_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parent selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context entry.allocation.extra parent selected head tail)
    (covered : GeneralBorrowGraph.RootsCover entry.allocation.extra)
    (forest : GeneralBorrowForest.Forest (source_normal_projection entry.allocation.extra default tracker.global.protectedTags).topology)
    (tagPresent : entry.allocation.extra.indexOfTag exprTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (aligned : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.data.size)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (support : Nat → Prop) (writable : Nat → Bool) (well : entry.allocation.extra.locations.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data entry.allocation.extra location
        (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags parent selected head tail support writable))
      offset (offset+len) entry.allocation.extra.locations)
    (allocationSize : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (valid : 1 < frame.locals.size)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
    (uncached : frame.locals[1].layout = none) (dead : frame.locals[1].value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let finalTree := GeneralBorrowExposedScopedInactiveWritableSharedArgumentCopy.finalTree entry.allocation.extra tracker exprTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    LenInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame valid output) borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (Provenance.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
  let cache := LenInstall.cacheFrame frame valid
  have cacheValid : 1 < cache.locals.size := by simpa [cache,LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame] using valid
  let live := RootArgumentEntry.liveFrame cache 1 cacheValid
  have liveValid : 1 < live.locals.size := by simpa [live,RootArgumentEntry.liveFrame] using cacheValid
  have cached : live.locals[1].layout = some SharedReferenceMetadata.sharedLayout := by
    simp [live,RootArgumentEntry.liveFrame,cache,LenInstall.cacheFrame,LocalOperands.cachedLayoutFrame,LenHelper.rawLayout]
  have checked := GeneralBorrowExposedScopedInactiveWritableSharedArgumentCopy.copy_argument options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits bounds frames live machine tracker enabled mode
    borrowFrame frameBorrow fresh parent selected head tail context covered forest tagPresent tagFresh noFree aligned fits support writable well owned allocationSize
    1 liveValid .uninit (by simp [live,RootArgumentEntry.liveFrame]) cached noClocks ghost shallow cachedAddress present race
    metadata notConstructed
    (LocalPlaces.localRuntimePlace frames.size live 1 SharedReferenceMetadata.sharedLayout).stackView rfl
  apply LenInstall.install_of_copy options limits remaining span debugOff frames frame machine value valid body identity callee
    uncached dead noClocks ghost _
  simpa only [live,cache,GeneralBorrowExposedScopedInactiveWritableSharedArgumentCopy.copiedFrame,GeneralBorrowExposedScopedSharedArgumentCopy.copiedFrame,LenInstall.resultFrame,LenInstall.cacheFrame,
    LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,
    TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.getElem_set_self,Array.set_set] using checked


theorem scoped_install_data
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset len : UInt64) (exprTag : BorTag)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (parent selected head : UniIndex) (tail : List UniIndex)
    (context : GeneralBorrowExposedKnownRootRangeData.Context entry.allocation.extra parent selected head tail)
    (covered : GeneralBorrowGraph.RootsCover entry.allocation.extra)
    (forest : GeneralBorrowForest.Forest (source_normal_projection entry.allocation.extra default tracker.global.protectedTags).topology)
    (tagPresent : entry.allocation.extra.indexOfTag exprTag = some parent)
    (tagFresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tracker.global.nextPointerTag)
    (noFree : entry.allocation.extra.tagMapping.deassigned.back? = none)
    (aligned : entry.allocation.extra.tagMapping.mapping.size = entry.allocation.extra.nodes.data.size)
    (fits : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (support : Nat → Prop) (writable : Nat → Bool) (well : entry.allocation.extra.locations.WellFormed)
    (owned : GeneralRangeMapOrigins.OwnedOn
      (fun location => Nonempty (GeneralBorrowExposedScopedInactiveWritableReadData.Data entry.allocation.extra location
        (TypedBorrowSteps.registeredGlobal tracker tracker.global.nextPointerTag).protectedTags parent selected head tail support writable))
      offset (offset+len) entry.allocation.extra.locations)
    (allocationSize : entry.allocation.extra.locations.size = entry.allocation.byteSize)
    (valid : 1 < frame.locals.size)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
    (uncached : frame.locals[1].layout = none) (dead : frame.locals[1].value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id exprTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len SharedReferenceMetadata.sharedLayout).imm
    let finalTree := GeneralBorrowExposedScopedInactiveWritableSharedArgumentCopy.finalTree entry.allocation.extra tracker exprTag offset len
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (LenInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value)
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (TypedBorrowSteps.registeredFrame (LenInstall.resultFrame frame valid output) borrowFrame id tracker.global.nextPointerTag) resultMachine) := by
  let activeTracker := {tracker with retagMode := .FnEntry}
  let activeMachine := {machine with borrowTracker := some activeTracker}
  have made := install_data options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    id entry base offset len exprTag positive nonzero signedFits bounds frames frame activeMachine
    activeTracker rfl rfl borrowFrame frameBorrow fresh parent selected head tail context covered forest tagPresent tagFresh noFree aligned fits support writable well owned
    allocationSize valid body identity callee uncached dead noClocks ghost shallow
    cachedAddress present race metadata notConstructed
  change MachineHooks.withRetagMode .FnEntry _ _ = _
  unfold MachineHooks.withRetagMode
  simp only [Storage.withCurrent]
  rw [enabled]
  dsimp only
  simp only [Storage.withCurrent,activeMachine,activeTracker] at made
  rw [made]
  simp only [Storage.withCurrent,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,
    ReferenceBorrowDriver.allocatedTracker,TypedBorrowSteps.registeredGlobal,activeMachine,activeTracker]
  rfl

end
end DuplicatePrefix.GeneralBorrowExposedScopedInactiveWritableLenInstall
