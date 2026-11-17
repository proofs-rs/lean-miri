import duplicate_prefix.PointerAddStatements
import duplicate_prefix.PointerOffsetRvalue
namespace DuplicatePrefix.PointerAddOffset
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
theorem offset
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (validPointer : (3 : Miri.MIR.LocalId) < frame.locals.size) (validCount : (4 : Miri.MIR.LocalId) < frame.locals.size)
    (validDest : (0 : Miri.MIR.LocalId) < frame.locals.size)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (pointerLive : frame.locals[3].value = .live (.immediate (.scalar
      (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))))
    (pointerCached : frame.locals[3].layout = some CopyCompilerFacts.destPointerLayout)
    (countLive : frame.locals[4].value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (countCached : frame.locals[4].layout = some RootCompilerFacts.usizeLayout)
    (destLive : frame.locals[0].value = .live (.immediate .uninit))
    (destUncached : frame.locals[0].layout = none)
    (sourceBody : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee)
    (location : frame.location = .mir ⟨0,4⟩)
    (noClocks : frame.extra.dataRace = none)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    let value : Immediate Provenance := .scalar (Scalar.fromPointer
      (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count))))
    ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent framesBefore frame machine) =
      (Storage.withCurrent framesBefore
        {(ActualLocalCopy.written frame 0 CopyCompilerFacts.destPointerLayout validDest value) with location := .mir ⟨0,5⟩}
        machine, .ok true) := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let value : Immediate Provenance := .scalar (Scalar.fromPointer config.access.runtime.base
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count))))
  let block := HelperCompilerFacts.addBody.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  let statement := block.statements[4]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[0]? = some block := by rw [sourceBody]; simp [block]
  have statementAt : block.statements[4]? = some statement := by simp [statement]
  have kind : statement.kind = .Assign ⟨0,#[]⟩ (.BinaryOp .Offset (.Move ⟨3,#[]⟩) (.Move ⟨4,#[]⟩)) := by with_unfolding_all rfl
  have normalized := PointerAddFacts.normalized_local0 frame sourceBody identity callee
  have lookup : PreparedReflection.actual.compiler.runtime.lookup 8 = .ok CopyCompilerFacts.destPointerLayout := by
    with_unfolding_all exact CopyCompilerFacts.dest_pointer_layout_eq
  have query := PointerAddFacts.compute_local framesBefore frame machine 0 8 CopyCompilerFacts.destPointerLayout normalized lookup
  have effect := PointerOffsetRvalue.evaluate options limits remaining span debugOff fuel validationFuel
    framesBefore frame machine 3 4 0 validPointer validCount validDest (by decide) (by decide)
    id tag base offset count entry pointerLive pointerCached countLive countCached destLive destUncached
    query noClocks ghostFalse shallow cached present positive fits bounds
  have afterLocation : (ActualLocalCopy.written frame 0 CopyCompilerFacts.destPointerLayout validDest value).location = .mir ⟨0,4⟩ := by
    simp [ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,location]
  exact SourceSteps.assign_exact config limits () framesBefore frame _ machine machine ⟨0,4⟩ block statement
    ⟨0,#[]⟩ (.BinaryOp .Offset (.Move ⟨3,#[]⟩) (.Move ⟨4,#[]⟩)) location blockAt statementAt kind effect afterLocation

#print axioms offset
end DuplicatePrefix.PointerAddOffset
