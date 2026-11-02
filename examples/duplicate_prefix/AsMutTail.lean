import duplicate_prefix.AsMutScopedInstall
import duplicate_prefix.AsMutFinish
namespace DuplicatePrefix.AsMutTail
noncomputable section
open Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory Miri.MIR Miri.TreeBorrows
open CanonicalConfigFacts ActualReferenceContext NestedConstruction BorrowRangeAccess NestedBorrowAccess
open AsMutCallCore
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def action (h : RootHooks) (value : Immediate Provenance) (destinationOp : OpTy Provenance) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let destinationMplace := match destinationOp.op with
    | .indirect place => some (MPlaceTy.mk place destinationOp.layout)
    | .immediate _ => none
  let frame ← h.getFrame
  let preamble ← match frame.location with
    | .unwinding span => pure span
    | .mir _ => throw (.invalidProgram "raw frame does not have preamble location")
  h.setFrame {frame with trackCallerArg := none}
  let (callerIndex, calleeIndex) ← h.withRetagMode () .FnEntry (AsMutInstall.action h value)
  spanAt h (← h.localSpan HelperCompilerFacts.asMutPtrBody.body 0)
  unless ← h.checkArgumentCompat () HelperCompilerFacts.asMutPtrAbi.ret HelperCompilerFacts.asMutPtrAbi.ret do
    throw (.undefinedBehavior "AbiMismatchReturn")
  if let some mplace := destinationMplace then h.protectArgument () mplace
  spanAt h preamble
  require (calleeIndex == HelperCompilerFacts.asMutPtrAbi.args.size) "mismatch between callee ABI and callee body arguments"
  if callerIndex < 1 then
    throw (.undefinedBehavior "calling a function with more arguments than it expected")
  h.afterFrameInit ()
  h.pushDone ()

theorem core_eq (h : RootHooks) (value : Immediate Provenance) (destination : RuntimeStackPlace Provenance) :
    AsMutCallCore.core h ⟨.immediate value,ActualReferenceMetadata.reference⟩ destination = (do
      let destinationOp ← h.placeToOp () destination
      h.pushRaw () HelperCompilerFacts.asMutPtrCall.callee HelperCompilerFacts.asMutPtrBody destination (.goto (some 7) .Continue)
      action h value destinationOp) := by
  unfold AsMutCallCore.core action AsMutInstall.action
  simp only [bind_assoc]
  rfl
theorem run
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (debugOff : options.place.debugAssertions = false) (cmp : ProjectionMetadataFacts.NullComparator)
    (dynamicFuel validityFuel : Nat) (fuelEq : options.place.dynamicFuel = dynamicFuel+1)
    (validationEq : options.limits.validation = validityFuel+1)
    (tags : Fin 6 → BorTag) (distinct : Function.Injective tags)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (capacity base offset len : UInt64)
    (tree : entry.allocation.extra = tree5 tags
      (partitionWithInside capacity offset (offset+len) rootLocation (location5 false)))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (nonzero : base+offset ≠ 0)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat+len.toNat ≤ capacity.toNat)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (borrowFrame : FrameState) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (mask : ProtectedStages.StageMask tags tracker.global.protectedTags 5 false)
    (nextTag : tracker.global.nextPointerTag = tags 5)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
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

    (old : Immediate Provenance) (destLayout : LocalLayout)
    (preamble : MIR.SpanRef) (located : frame.location = .unwinding preamble)
    (track : frame.trackCallerArg = none)
    (dead0 : (frame.locals[0]'(by have bound : (1 : Nat) < frame.locals.size := valid; omega)).value = .dead) :
    let cfg := config options remaining span
    let value := (RetagReferencePlace.sliceValue cfg.access.runtime.base
      (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
    let finalTree := nestedTree tags (partitionWithInside capacity offset (offset+len) rootLocation (nestedLocation false))
    let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
    action (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      value ⟨.immediate old,destLayout⟩ (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames
        (AsMutDone.doneFrame {(AsMutInstall.resultFrame frame valid value
          (RetagReferencePlace.sliceValue cfg.access.runtime.base
            (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
          borrowFrame id tracker.global.nextPointerTag) with location := .unwinding preamble}) resultMachine) := by
  have bound : (1 : Nat) < frame.locals.size := valid
  let h := ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits
  let value := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id (tags 4)) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let adjusted := (RetagReferencePlace.sliceValue (config options remaining span).access.runtime.base
    (Pointer.new (.concrete id tracker.global.nextPointerTag) (Size.ofBytes (base+offset))) len ActualReferenceMetadata.reference).imm
  let result := AsMutInstall.resultFrame frame valid value adjusted borrowFrame id tracker.global.nextPointerTag
  let finalTree := nestedTree tags (partitionWithInside capacity offset (offset+len) rootLocation (nestedLocation false))
  let resultMachine := {TypedBorrowSteps.registeredMachine (ReferenceBorrowDriver.allocatedMachine machine tracker fresh)
      (ReferenceBorrowDriver.allocatedTracker tracker fresh) tracker.global.nextPointerTag with
      memory := RetagEntry.updatedMemory machine.memory id entry finalTree}
  have same : {frame with trackCallerArg := none} = frame := by rw [←track]
  have getframe := CallEntryLocals.get_frame options limits (remaining+1) span frames frame machine
  have setframe := CallEntryLocals.set_frame options limits (remaining+1) span frames frame frame machine
  have installed := AsMutScopedInstall.install options limits remaining span ctx debugOff cmp dynamicFuel validityFuel fuelEq validationEq
    tags distinct id entry capacity base offset len tree allocationSize positive nonzero signedFits bounds frames frame machine tracker enabled
    defaultMode borrowFrame frameBorrow mask nextTag fresh valid body identity callee dead uncached noClocks ghost shallow
    cachedAddress present race metadata notConstructed
  have resultBody : result.body = HelperCompilerFacts.asMutPtrBody.body := body
  have resultIdentity : result.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity := identity
  have resultCallee : result.functionInstance = HelperCompilerFacts.asMutPtrCall.callee := callee
  have resultValid : 0 < result.locals.size := by
    simp only [result,AsMutInstall.resultFrame,AsMutInstall.cacheFrame,AsMutInstall.spanFrame,
      LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,AsMutPtrArgumentCopy.copiedFrame,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.size_set]
    omega
  have resultDead : result.locals[0].value = .dead := by
    simpa [result,AsMutInstall.resultFrame,AsMutInstall.cacheFrame,AsMutInstall.spanFrame,
      LocalOperands.cachedLayoutFrame,RootArgumentEntry.liveFrame,AsMutPtrArgumentCopy.copiedFrame,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.getElem_set] using dead0
  have resultClocks : result.extra.dataRace = none := noClocks
  have finished := AsMutFinish.finish options limits (remaining+1) span frames result resultMachine preamble
    resultBody resultIdentity resultCallee resultValid resultDead resultClocks
  unfold action
  simp only [bind,EStateM.bind]
  rw [getframe]
  dsimp only
  rw [located]
  simp only [pure,Pure.pure,EStateM.pure,bind,EStateM.bind]
  rw [←located,same,setframe]
  dsimp only
  rw [installed]
  dsimp only
  change AsMutFinish.action h preamble (Storage.withCurrent frames result resultMachine) = _
  exact finished

#print axioms run
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``run) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved asmut tail dependency {dependency}"
end
end DuplicatePrefix.AsMutTail
