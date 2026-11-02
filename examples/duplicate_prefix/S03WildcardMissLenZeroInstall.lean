import duplicate_prefix.GlobalAddressLiveErrorExclusion
import duplicate_prefix.S03WildcardMissLenZeroArgumentCopy
import duplicate_prefix.LenZeroInstall
import duplicate_prefix.LenInstall
import duplicate_prefix.LenZeroArgumentCopy
namespace DuplicatePrefix.S03WildcardMissLenZeroInstall
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem integer_zero
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (address : UInt64) (nonzero : address ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (mode : tracker.retagMode = .FnEntry)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (valid : 1 < frame.locals.size)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
    (uncached : frame.locals[1].layout = none) (dead : frame.locals[1].value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (miss : machine.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup machine.memory) = .ok none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm
    let resultMachine := ReferenceBorrowDriver.allocatedMachine machine tracker fresh
    LenInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (LenInstall.resultFrame frame valid output) resultMachine) := by
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm
  let cache := LenInstall.cacheFrame frame valid
  have cacheValid : 1 < cache.locals.size := by simpa [cache,LenInstall.cacheFrame,LenInstall.spanFrame,LocalOperands.cachedLayoutFrame] using valid
  let live := RootArgumentEntry.liveFrame cache 1 cacheValid
  have liveValid : 1 < live.locals.size := by simpa [live,RootArgumentEntry.liveFrame] using cacheValid
  have cached : live.locals[1].layout = some SharedReferenceMetadata.sharedLayout := by
    simp [live,RootArgumentEntry.liveFrame,cache,LenInstall.cacheFrame,LocalOperands.cachedLayoutFrame,LenHelper.rawLayout]
  have checked := S03WildcardMissLenZeroArgumentCopy.integer_zero options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    address nonzero frames live machine
    tracker enabled mode fresh 1 liveValid .uninit
    (by simp [live,RootArgumentEntry.liveFrame]) cached noClocks ghost shallow addressMode miss metadata notConstructed
    (LocalPlaces.localRuntimePlace frames.size live 1 SharedReferenceMetadata.sharedLayout).stackView rfl
  apply LenInstall.install_of_copy options limits remaining span debugOff frames frame machine value valid body identity callee
    uncached dead noClocks ghost _
  simpa only [live,cache,S03WildcardMissLenZeroArgumentCopy.copiedFrame,LenInstall.resultFrame,LenInstall.cacheFrame,
    LenInstall.spanFrame,LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,
    TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.getElem_set_self,Array.set_set] using checked

theorem integer_zero_scoped
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (address : UInt64) (nonzero : address ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (valid : 1 < frame.locals.size)
    (body : frame.body = LenHelper.body.body)
    (identity : frame.bodyIdentity = LenHelper.body.identity)
    (callee : frame.functionInstance = LenHelper.resolved.callee)
    (uncached : frame.locals[1].layout = none) (dead : frame.locals[1].value = .dead)
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (addressMode : machine.user.addresses.provenanceMode ≠ .strict)
    (miss : machine.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup machine.memory) = .ok none)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm
    let output := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base (Pointer.new .wildcard (Size.ofBytes address)) 0 SharedReferenceMetadata.sharedLayout).imm
    let resultMachine := ReferenceBorrowDriver.allocatedMachine machine tracker fresh
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (LenInstall.action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) value)
      (Storage.withCurrent frames frame machine) =
      .ok (1,1) (Storage.withCurrent frames
        (LenInstall.resultFrame frame valid output) resultMachine) := by
  let activeTracker := {tracker with retagMode := .FnEntry}
  let activeMachine := {machine with borrowTracker := some activeTracker}
  have made := integer_zero options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    address nonzero frames frame activeMachine
    activeTracker rfl rfl fresh valid body identity callee uncached dead noClocks ghost shallow
    addressMode miss metadata notConstructed
  change MachineHooks.withRetagMode .FnEntry _ _ = _
  unfold MachineHooks.withRetagMode
  simp only [Storage.withCurrent]
  rw [enabled]
  dsimp only
  simp only [Storage.withCurrent,activeMachine,activeTracker] at made
  rw [made]
  simp only [Storage.withCurrent,TypedBorrowSteps.registeredMachine,ReferenceBorrowDriver.allocatedMachine,
    ReferenceBorrowDriver.allocatedTracker,TypedBorrowSteps.registeredGlobal,activeMachine,activeTracker]
  all_goals rfl

end
end DuplicatePrefix.S03WildcardMissLenZeroInstall
