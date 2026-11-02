import duplicate_prefix.RootReferenceWrite
import duplicate_prefix.RootReferenceZeroValidator
namespace DuplicatePrefix.RootReferenceZeroWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo RootReferenceWrite
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem live_zero_cached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (shared : Bool)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (base offset : UInt64) (parentTag : BorTag)
    (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (currentMode : tracker.retagMode = mode shared)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (old : Immediate Provenance) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some (layout shared))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (finalTree : BorrowTree)
    (child : entry.allocation.extra.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 0) (initial shared)) (policy shared).outsidePermission false = ⟨finalTree,.ok ()⟩)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let value := RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 (layout shared)
    let output := RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 (layout shared)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).writeImmediate
      () value.imm (LocalPlaces.localRuntimePlace frames.size frame localId (layout shared))
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (written frame localId output.imm valid) resultMachine) := by
  let cfg := config options remaining span
  let value := RetagReferencePlace.sliceValue cfg.access.runtime.base
    (Pointer.new (Provenance.concrete id parentTag) (Size.ofBytes (base+offset))) 0 (layout shared)
  let post := written frame localId value.imm valid
  have postValid : localId < post.locals.size := by simpa [post,written] using valid
  have postLive : post.locals[localId].value = .live (.immediate value.imm) := by simp [post,written]
  have postCached : post.locals[localId].layout = some (layout shared) := by simpa [post,written] using cached
  have info := RootReferenceInfo.facts options remaining span ctx shared
  have validator := RootReferenceZeroValidator.live_zero options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    (layout shared) (mutability shared) (mode shared) (policy shared) (initial shared) info.protection info.associated info.initialState
    info.created info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference info.sized info.readable
    (name shared) info.named info.classified id entry base offset parentTag nonzero
    frames post machine tracker enabled currentMode fresh localId postValid postLive postCached ghost shallow
    cachedAddress present finalTree child metadata notConstructed
  have finalFrame (newValue : Immediate Provenance) : written post localId newValue postValid = written frame localId newValue valid := by
    simp [post,written,Array.set_set]
  apply of_validation options limits remaining span debugOff validityFuel validationFuel frames frame machine
    localId old value.imm (layout shared) valid live cached info.sized noClocks ghost shallow
  simpa only [post,value,written,Array.getElem_set_self,Array.set_set] using validator


theorem nonlive_zero_cached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (shared : Bool)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (id : AllocId) (allocation : AllocationInfo)
    (base offset : UInt64) (parentTag : BorTag)
    (nonzero : base+offset ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (allocationInfo : machine.memory.getAllocInfo id = .ok allocation)
    (nonlive : allocation.kind ≠ .liveData)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (currentMode : tracker.retagMode = mode shared)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (old : Immediate Provenance) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some (layout shared))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let value := RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) 0 (layout shared)
    let output := RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) 0 (layout shared)
    let resultMachine := ReferenceBorrowDriver.allocatedMachine machine tracker fresh
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).writeImmediate
      () value.imm (LocalPlaces.localRuntimePlace frames.size frame localId (layout shared))
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (written frame localId output.imm valid) resultMachine) := by
  let cfg := config options remaining span
  let value := RetagReferencePlace.sliceValue cfg.access.runtime.base
    (Pointer.new (Provenance.concrete id parentTag) (Size.ofBytes (base+offset))) 0 (layout shared)
  let post := written frame localId value.imm valid
  have postValid : localId < post.locals.size := by simpa [post,written] using valid
  have postLive : post.locals[localId].value = .live (.immediate value.imm) := by simp [post,written]
  have postCached : post.locals[localId].layout = some (layout shared) := by simpa [post,written] using cached
  have info := RootReferenceInfo.facts options remaining span ctx shared
  have validator := RootReferenceZeroValidator.nonlive_zero options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    (layout shared) (mutability shared) (mode shared) (policy shared) (initial shared) info.protection info.associated info.initialState
    info.created info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference info.sized info.readable
    (name shared) info.named info.classified id allocation base offset parentTag nonzero
    frames post machine allocationInfo nonlive tracker enabled currentMode fresh localId postValid postLive postCached ghost shallow
    cachedAddress metadata notConstructed
  have finalFrame (newValue : Immediate Provenance) : written post localId newValue postValid = written frame localId newValue valid := by
    simp [post,written,Array.set_set]
  apply of_validation options limits remaining span debugOff validityFuel validationFuel frames frame machine
    localId old value.imm (layout shared) valid live cached info.sized noClocks ghost shallow
  simpa only [post,value,written,Array.getElem_set_self,Array.set_set] using validator


theorem integer_zero_cached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (shared : Bool)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationFuel : options.limits.validation = validityFuel+1)
    (address : UInt64) (nonzero : address ≠ 0)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (currentMode : tracker.retagMode = mode shared)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (old : Immediate Provenance) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some (layout shared))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let value := RetagReferencePlace.integerSliceValue address 0 (layout shared)
    let output := RetagReferencePlace.integerSliceValue address 0 (layout shared)
    let resultMachine := ReferenceBorrowDriver.allocatedMachine machine tracker fresh
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).writeImmediate
      () value.imm (LocalPlaces.localRuntimePlace frames.size frame localId (layout shared))
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (written frame localId output.imm valid) resultMachine) := by
  let cfg := config options remaining span
  let value := RetagReferencePlace.integerSliceValue address 0 (layout shared)
  let post := written frame localId value.imm valid
  have postValid : localId < post.locals.size := by simpa [post,written] using valid
  have postLive : post.locals[localId].value = .live (.immediate value.imm) := by simp [post,written]
  have postCached : post.locals[localId].layout = some (layout shared) := by simpa [post,written] using cached
  have info := RootReferenceInfo.facts options remaining span ctx shared
  have validator := RootReferenceZeroValidator.integer_zero options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    (layout shared) (mutability shared) (mode shared) (policy shared) (initial shared) info.protection info.associated info.initialState
    info.created info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference info.sized info.readable
    (name shared) info.named info.classified address nonzero
    frames post machine tracker enabled currentMode fresh localId postValid postLive postCached ghost shallow
    metadata notConstructed
  have finalFrame (newValue : Immediate Provenance) : written post localId newValue postValid = written frame localId newValue valid := by
    simp [post,written,Array.set_set]
  apply of_validation options limits remaining span debugOff validityFuel validationFuel frames frame machine
    localId old value.imm (layout shared) valid live cached info.sized noClocks ghost shallow
  simpa only [post,value,written,Array.getElem_set_self,Array.set_set] using validator



open Lean Elab Command in
run_cmd do
  for declaration in [``live_zero_cached, ``nonlive_zero_cached, ``integer_zero_cached] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved axiom {dependency}"
end
end DuplicatePrefix.RootReferenceZeroWrite
