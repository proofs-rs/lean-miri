import duplicate_prefix.ActualOffset
import duplicate_prefix.ActualLocalCopy
import duplicate_prefix.RootOperandMove
import duplicate_prefix.RootPointerWrite
import duplicate_prefix.RvalueDispatch
import duplicate_prefix.ImmediateReadProof
namespace DuplicatePrefix.PointerOffsetRvalue
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem evaluate
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointerId countId destId : Miri.MIR.LocalId)
    (validPointer : pointerId < frame.locals.size) (validCount : countId < frame.locals.size)
    (validDest : destId < frame.locals.size)
    (differentPointer : destId ≠ pointerId) (differentCount : destId ≠ countId)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (pointerLive : frame.locals[pointerId].value = .live (.immediate (.scalar
      (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))))
    (pointerCached : frame.locals[pointerId].layout = some CopyCompilerFacts.destPointerLayout)
    (countLive : frame.locals[countId].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (countCached : frame.locals[countId].layout = some RootCompilerFacts.usizeLayout)
    (destLive : frame.locals[destId].value = .live (.immediate .uninit))
    (destUncached : frame.locals[destId].layout = none)
    (query : CompilerFrameContext.computeLocalLayout PreparedReflection.actual.compiler destId
      (Storage.withCurrent framesBefore frame machine) =
        .ok CopyCompilerFacts.destPointerLayout (Storage.withCurrent framesBefore frame machine))
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    let value := .scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count))))
    evalRvalueIntoPlace
      (ExecutionMachine.rvalueHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits) ()
      (.BinaryOp .Offset (.Move ⟨pointerId,#[]⟩) (.Move ⟨countId,#[]⟩)) ⟨destId,#[]⟩
      (Storage.withCurrent framesBefore frame machine) =
    .ok () (Storage.withCurrent framesBefore
      (ActualLocalCopy.written frame destId CopyCompilerFacts.destPointerLayout validDest value) machine) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let hooks := ExecutionMachine.rvalueHooks config limits
  let cachedFrame := LocalPlaces.cachePlaceLayout frame destId CopyCompilerFacts.destPointerLayout validDest
  let state0 := Storage.withCurrent framesBefore frame machine
  let state1 := Storage.withCurrent framesBefore cachedFrame machine
  let dest := LocalPlaces.localRuntimePlace framesBefore.size cachedFrame destId CopyCompilerFacts.destPointerLayout
  let pointer := Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset))
  let resultPointer := Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count))
  let left := PointerDispatch.pointerImmediate config.access.runtime.base pointer CopyCompilerFacts.destPointerLayout
  let right : RvalueImmTy Provenance := ScalarOperations.usizeImmediate count RootCompilerFacts.usizeLayout
  let result := PointerDispatch.pointerImmediate config.access.runtime.base resultPointer CopyCompilerFacts.destPointerLayout
  have destEval := ActualLocalPlace.uncached options limits (remaining+1) span debugOff framesBefore frame machine
    destId CopyCompilerFacts.destPointerLayout validDest destUncached RootRawPointerValidity.mut_pointer_sized query
  have pointerValid : pointerId < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validPointer
  have countValid : countId < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validCount
  have pointerLive' : cachedFrame.locals[pointerId].value = .live (.immediate left.imm) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,differentPointer,left,PointerDispatch.pointerImmediate,pointer,config] using pointerLive
  have pointerCached' : cachedFrame.locals[pointerId].layout = some CopyCompilerFacts.destPointerLayout := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,differentPointer] using pointerCached
  have countLive' : cachedFrame.locals[countId].value = .live (.immediate right.imm) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,differentCount,right,ScalarOperations.usizeImmediate] using countLive
  have countCached' : cachedFrame.locals[countId].layout = some RootCompilerFacts.usizeLayout := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout,Array.getElem_set,differentCount] using countCached
  have leftOperand := RootOperandMove.move_cached_local options limits (remaining+1) span debugOff framesBefore cachedFrame machine
    pointerId left.imm CopyCompilerFacts.destPointerLayout (OperandPath.rvalue "left")
    (if BinOp.Offset.leftHomogeneous then some (hooks.placeLayout dest) else none)
    pointerValid pointerLive' pointerCached' (by decide +kernel) noClocks ghostFalse
  have rightOperand := RootOperandMove.move_cached_local options limits (remaining+1) span debugOff framesBefore cachedFrame machine
    countId right.imm RootCompilerFacts.usizeLayout (OperandPath.rvalue "right")
    (if BinOp.Offset.rightHomogeneous then some left.layout else none)
    countValid countLive' countCached' (by decide +kernel) noClocks ghostFalse
  have retain := CanonicalConfigFacts.actual_retain_touched options () (remaining+1) span
  have leftRead := ImmediateReadProof.read_scalar_immediate config.access state1
    (Scalar.fromPointer config.access.runtime.base pointer) CopyCompilerFacts.destPointerLayout
    (CopyCompilerFacts.initialized_scalar_exists _ CopyCompilerFacts.primitive_layouts_initialized.2.2.1) (by rw [retain])
  have rightRead := ImmediateReadProof.read_scalar_immediate config.access state1
    (.fromScalarInt (.ofUInt64 count)) RootCompilerFacts.usizeLayout
    (CopyCompilerFacts.initialized_scalar_exists _ CopyCompilerFacts.primitive_layouts_initialized.2.2.2) (by rw [retain])
  have operation := ActualOffset.byte_offset options (remaining+1) span state1 id tag base offset count entry
    cached present positive fits bounds
  have destValid' : destId < cachedFrame.locals.size := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using validDest
  have destLive' : cachedFrame.locals[destId].value = .live (.immediate .uninit) := by
    simpa [cachedFrame,LocalPlaces.cachePlaceLayout] using destLive
  have destCache' : cachedFrame.locals[destId].layout = some CopyCompilerFacts.destPointerLayout := by
    simp [cachedFrame,LocalPlaces.cachePlaceLayout]
  have write := RootPointerWrite.write_mut_pointer_shallow options limits remaining span debugOff fuel validationFuel
    framesBefore cachedFrame machine destId .uninit (Scalar.fromPointer config.access.runtime.base resultPointer)
    destValid' destLive' destCache' noClocks ghostFalse shallow
  exact RvalueDispatch.binaryOp hooks () .Offset (.Move ⟨pointerId,#[]⟩) (.Move ⟨countId,#[]⟩)
    ⟨destId,#[]⟩ dest ⟨.immediate left.imm,left.layout⟩ ⟨.immediate right.imm,right.layout⟩
    left right result state0 state1 state1 state1 state1 state1 state1 _
    destEval leftOperand leftRead rightOperand rightRead operation rfl write

#print axioms evaluate
end DuplicatePrefix.PointerOffsetRvalue
