import duplicate_prefix.RootReferenceInfo
import duplicate_prefix.RootUsizeWrite
namespace DuplicatePrefix.RootReferenceWrite
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext RootReferenceInfo
noncomputable section
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def written (frame : CompilerFrameContext.ActualFrame) (localId : MIR.LocalId) (value : Immediate Provenance)
    (valid : localId < frame.locals.size) :=
  {frame with locals := (frame.locals.set localId {value := .live (.immediate value),layout := frame.locals[localId].layout} valid)}

theorem of_validation
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (localId : MIR.LocalId) (old value : Immediate Provenance) (reference : LocalLayout)
    (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some reference)
    (sized : reference.layout.isSized = true) (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (after : RootState)
    (validation : ValidityMachine.validateRuntime
      (PreparedContracts.actualConfig options () remaining span).validity () (fuel+1)
      (LocalPlaces.localRuntimePlace frames.size (written frame localId value valid) localId reference) true
      (Storage.withCurrent frames (written frame localId value valid) machine) = .ok () after) :
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).writeImmediate
      () value (LocalPlaces.localRuntimePlace frames.size frame localId reference)
      (Storage.withCurrent frames frame machine) = .ok () after := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let place := (ExecutionMachine.projectionHooks (ExecutionMachine.withValidation cfg limits)).place
  let post := Storage.withCurrent frames (written frame localId value valid) machine
  have fields := CanonicalConfigFacts.actual_fields options () (remaining+1) span
  have physical := RootUsizeWrite.write_local_no_validate options limits (remaining+1) span debugOff frames frame machine
    localId old value reference valid live sized noClocks ghost
  have enforced : place.enforceValidity () reference post = .ok true post := by
    change cfg.projection.place.enforceValidity () reference post = _
    rw [fields.projectionEnforce]
    simp [ValidityMachine.enforceValidity,post,written,Storage.withCurrent,shallow,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  have validated : place.validate () (LocalPlaces.localRuntimePlace frames.size frame localId reference) post = .ok () after := by
    change cfg.projection.place.validate () _ post = _
    rw [fields.projectionValidate,CanonicalConfigFacts.actual_validate_successor,validationFuel]
    exact validation
  change writePlaceImmediate place () value (LocalPlaces.localRuntimePlace frames.size frame localId reference) _ = _
  unfold writePlaceImmediate
  simp only [bind,EStateM.bind]
  rw [physical]
  simp only [bind,EStateM.bind]
  erw [enforced]
  exact validated

theorem positive_cached
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false)
    (cmp : ProjectionMetadataFacts.NullComparator) (shared : Bool)
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
    (currentMode : tracker.retagMode = mode shared)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (localId : MIR.LocalId) (old : Immediate Provenance) (valid : localId < frame.locals.size)
    (live : frame.locals[localId].value = .live (.immediate old))
    (cached : frame.locals[localId].layout = some (layout shared))
    (noClocks : frame.extra.dataRace = none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (cachedAddress : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (race : machine.dataRace = none)
    (parentTree finalTree : BorrowTree)
    (readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild (Size.ofBytes offset) (.concrete parentTag) tracker.global.nextPointerTag
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes len) (initial shared)) (policy shared).outsidePermission false = ⟨finalTree,.ok ()⟩)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    let cfg := config options remaining span
    let value := RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id parentTag) (Size.ofBytes (base+offset))) len (layout shared)
    let output := RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len (layout shared)
    let resultMachine := {ReferenceBorrowDriver.allocatedMachine machine tracker fresh with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).writeImmediate
      () value.imm (LocalPlaces.localRuntimePlace frames.size frame localId (layout shared))
      (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames (written frame localId output.imm valid) resultMachine) := by
  let cfg := config options remaining span
  let value := RetagReferencePlace.sliceValue cfg.access.runtime.base
    (Pointer.new (Provenance.concrete id parentTag) (Size.ofBytes (base+offset))) len (layout shared)
  let post := written frame localId value.imm valid
  have postValid : localId < post.locals.size := by simpa [post,written] using valid
  have postLive : post.locals[localId].value = .live (.immediate value.imm) := by simp [post,written]
  have postCached : post.locals[localId].layout = some (layout shared) := by simpa [post,written] using cached
  have info := RootReferenceInfo.facts options remaining span ctx shared
  have validator := RootReferenceValidator.positive options remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq
    (layout shared) (mutability shared) (mode shared) (policy shared) (initial shared) info.protection info.associated info.initialState
    info.created info.shape info.pointeeQuery info.unpin info.unsafeUnpin info.frozen info.dereference info.sized info.readable
    (name shared) info.named info.classified id entry base offset len parentTag positive nonzero signedFits bounds
    frames post machine tracker enabled currentMode fresh localId postValid postLive postCached ghost shallow
    cachedAddress present race parentTree finalTree readTree readDone child metadata notConstructed
  have finalFrame (newValue : Immediate Provenance) : written post localId newValue postValid = written frame localId newValue valid := by
    simp [post,written,Array.set_set]
  apply of_validation options limits remaining span debugOff validityFuel validationFuel frames frame machine
    localId old value.imm (layout shared) valid live cached info.sized noClocks ghost shallow
  simpa only [post,value,written,Array.getElem_set_self,Array.set_set] using validator

#print axioms positive_cached
open Lean Elab Command in
run_cmd do
  for declaration in [``of_validation, ``positive_cached] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved axiom {dependency}"
end
end DuplicatePrefix.RootReferenceWrite
