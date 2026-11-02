import duplicate_prefix.PointerAddOffset
import duplicate_prefix.SourceSteps
namespace DuplicatePrefix.PointerAddBody
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem actual_seven_statements
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (framesBefore : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (size : frame.locals.size = 5)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate (.scalar
      (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))))))
    (cached1 : (frame.locals[1]'(by omega)).layout = some CopyCompilerFacts.destPointerLayout)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (dead3 : (frame.locals[3]'(by omega)).value = .dead)
    (uncached3 : (frame.locals[3]'(by omega)).layout = none)
    (dead4 : (frame.locals[4]'(by omega)).value = .dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout = none)
    (sourceBody : frame.body = HelperCompilerFacts.addBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.addBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.addCall.callee)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghostFalse : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ f1 f2 f3 f4 f5 f6 done : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore frame machine) =
        (Storage.withCurrent framesBefore f1 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f1 machine) =
        (Storage.withCurrent framesBefore f2 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f2 machine) =
        (Storage.withCurrent framesBefore f3 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f3 machine) =
        (Storage.withCurrent framesBefore f4 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f4 machine) =
        (Storage.withCurrent framesBefore f5 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f5 machine) =
        (Storage.withCurrent framesBefore f6 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent framesBefore f6 machine) =
        (Storage.withCurrent framesBefore done machine,.ok true) ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧
      done.functionInstance = frame.functionInstance ∧ done.extra = frame.extra ∧
      done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧
      done.locals[1]? = frame.locals[1]? ∧ done.locals[2]? = frame.locals[2]? ∧
      done.locals.size = 5 ∧ done.location = .mir ⟨0,7⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar
        (Scalar.fromPointer config.access.runtime.base
          (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count)))))),
        some CopyCompilerFacts.destPointerLayout⟩ ∧
      (done.locals[3]?.map (·.value)) = some .dead ∧
      (done.locals[4]?.map (·.value)) = some .dead := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let raw : Scalar Provenance := Scalar.fromPointer config.access.runtime.base
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))
  let resultRaw : Scalar Provenance := Scalar.fromPointer config.access.runtime.base
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count)))
  have valid0 : (0 : Miri.MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have valid1 : (1 : Miri.MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have valid3 : (3 : Miri.MIR.LocalId) < frame.locals.size := by rw [size]; decide
  have valid4 : (4 : Miri.MIR.LocalId) < frame.locals.size := by rw [size]; decide
  let block := HelperCompilerFacts.addBody.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  have blockAt : HelperCompilerFacts.addBody.body.basicBlocks[0]? = some block := by simp [block]
  let stmt0 := block.statements[0]'(by with_unfolding_all decide +kernel)
  have stmtAt0 : block.statements[0]? = some stmt0 := by simp [stmt0]
  have kind0 : stmt0.kind = .StorageLive 3 := by with_unfolding_all rfl
  let stmt2 := block.statements[2]'(by with_unfolding_all decide +kernel)
  have stmtAt2 : block.statements[2]? = some stmt2 := by simp [stmt2]
  have kind2 : stmt2.kind = .StorageLive 4 := by with_unfolding_all rfl
  let stmt5 := block.statements[5]'(by with_unfolding_all decide +kernel)
  have stmtAt5 : block.statements[5]? = some stmt5 := by simp [stmt5]
  have kind5 : stmt5.kind = .StorageDead 4 := by with_unfolding_all rfl
  let stmt6 := block.statements[6]'(by with_unfolding_all decide +kernel)
  have stmtAt6 : block.statements[6]? = some stmt6 := by simp [stmt6]
  have kind6 : stmt6.kind = .StorageDead 3 := by with_unfolding_all rfl
  have trivial8 : config.lifecycle.storage.veryTriviallySized 8 = .ok true := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).storage]
    decide +kernel
  have trivial5 : config.lifecycle.storage.veryTriviallySized 5 = .ok true := by
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).storage]
    exact RootCompilerFacts.root_storage_trivial_usize
  let f1 := SourceSteps.liveFrame frame ⟨0,0⟩ 3 valid3
  have step1 := SourceSteps.storage_live_exact config limits () framesBefore frame machine ⟨0,0⟩ block stmt0 3 8
    location (by rw [sourceBody]; exact blockAt) stmtAt0 kind0 valid3
    (by rw [sourceBody]; with_unfolding_all rfl) trivial8 dead3 noClocks
  have size1 : f1.locals.size = 5 := by simp [f1,SourceSteps.liveFrame,size]
  have v11 : (1 : Miri.MIR.LocalId) < f1.locals.size := by rw [size1]; decide
  have v13 : (3 : Miri.MIR.LocalId) < f1.locals.size := by rw [size1]; decide
  let f2 := {(ActualLocalCopy.written f1 3 CopyCompilerFacts.destPointerLayout v13 (.scalar raw)) with location := .mir ⟨0,2⟩}
  have step2 := PointerAddStatements.copy_pointer options limits remaining span debugOff fuel validationFuel
    framesBefore f1 machine raw v11 v13
    (by simpa [f1,SourceSteps.liveFrame,Array.getElem_set,raw,config] using live1)
    (by simpa [f1,SourceSteps.liveFrame,Array.getElem_set] using cached1)
    (by simp [f1,SourceSteps.liveFrame])
    (by simpa [f1,SourceSteps.liveFrame] using uncached3)
    sourceBody identity callee rfl noClocks tracker tracked defaultMode ghostFalse shallow
  have size2 : f2.locals.size = 5 := by simp [f2,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size1]
  have v24 : (4 : Miri.MIR.LocalId) < f2.locals.size := by rw [size2]; decide
  let f3 := SourceSteps.liveFrame f2 ⟨0,2⟩ 4 v24
  have step3 := SourceSteps.storage_live_exact config limits () framesBefore f2 machine ⟨0,2⟩ block stmt2 4 5
    rfl (by change frame.body.basicBlocks[0]? = _; rw [sourceBody]; exact blockAt) stmtAt2 kind2 v24
    (by change frame.body.locals[4]? = _;rw [sourceBody];with_unfolding_all rfl) trivial5
    (by simpa [f2,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f1,SourceSteps.liveFrame,Array.getElem_set] using dead4) noClocks
  have size3 : f3.locals.size = 5 := by simp [f3,SourceSteps.liveFrame,size2]
  have v32 : (2 : Miri.MIR.LocalId) < f3.locals.size := by rw [size3]; decide
  have v34 : (4 : Miri.MIR.LocalId) < f3.locals.size := by rw [size3]; decide
  let f4 := {(ActualLocalCopy.written f3 4 RootCompilerFacts.usizeLayout v34 (.scalar (.fromScalarInt (.ofUInt64 count)))) with location := .mir ⟨0,4⟩}
  have step4 := PointerAddStatements.copy_count options limits remaining span debugOff fuel validationFuel
    framesBefore f3 machine count v32 v34
    (by simpa [f3,SourceSteps.liveFrame,f2,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f1,Array.getElem_set] using live2)
    (by simpa [f3,SourceSteps.liveFrame,f2,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f1,Array.getElem_set] using cached2)
    (by simp [f3,SourceSteps.liveFrame])
    (by simpa [f3,SourceSteps.liveFrame,f2,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f1,Array.getElem_set] using uncached4)
    sourceBody identity callee rfl noClocks tracker tracked defaultMode ghostFalse shallow
  have size4 : f4.locals.size = 5 := by simp [f4,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size3]
  have v40 : (0 : Miri.MIR.LocalId) < f4.locals.size := by rw [size4]; decide
  have v43 : (3 : Miri.MIR.LocalId) < f4.locals.size := by rw [size4]; decide
  have v44 : (4 : Miri.MIR.LocalId) < f4.locals.size := by rw [size4]; decide
  let f5 := {(ActualLocalCopy.written f4 0 CopyCompilerFacts.destPointerLayout v40 (.scalar resultRaw)) with location := .mir ⟨0,5⟩}
  have step5 := PointerAddOffset.offset options limits remaining span debugOff fuel validationFuel framesBefore f4 machine
    v43 v44 v40 id tag base offset count entry
    (by simp [f4,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f3,SourceSteps.liveFrame,f2,Array.getElem_set,raw,config])
    (by simp [f4,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f3,SourceSteps.liveFrame,f2,Array.getElem_set])
    (by simp [f4,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout])
    (by simp [f4,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout])
    (by simpa [f4,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f3,SourceSteps.liveFrame,f2,f1,Array.getElem_set] using live0)
    (by simpa [f4,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f3,SourceSteps.liveFrame,f2,f1,Array.getElem_set] using uncached0)
    sourceBody identity callee rfl noClocks ghostFalse shallow cached present positive fits bounds
  have size5 : f5.locals.size = 5 := by simp [f5,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,size4]
  have v54 : (4 : Miri.MIR.LocalId) < f5.locals.size := by rw [size5]; decide
  let f6 := SourceSteps.deadFrame f5 ⟨0,5⟩ 4 v54
  have step6 := SourceSteps.storage_dead_exact config limits () framesBefore f5 machine ⟨0,5⟩ block stmt5 4
    (.scalar (.fromScalarInt (.ofUInt64 count))) rfl
    (by change frame.body.basicBlocks[0]? = _;rw [sourceBody];exact blockAt) stmtAt5 kind5 v54 (by decide)
    (by simp [f5,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f4,Array.getElem_set])
  have size6 : f6.locals.size = 5 := by simp [f6,SourceSteps.deadFrame,size5]
  have v63 : (3 : Miri.MIR.LocalId) < f6.locals.size := by rw [size6]; decide
  let done := SourceSteps.deadFrame f6 ⟨0,6⟩ 3 v63
  have step7 := SourceSteps.storage_dead_exact config limits () framesBefore f6 machine ⟨0,6⟩ block stmt6 3
    (.scalar raw) rfl
    (by change frame.body.basicBlocks[0]? = _;rw [sourceBody];exact blockAt) stmtAt6 kind6 v63 (by decide)
    (by simp [f6,SourceSteps.deadFrame,f5,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f4,f3,SourceSteps.liveFrame,f2,Array.getElem_set])
  refine ⟨f1,f2,f3,f4,f5,f6,done,step1,step2,step3,step4,step5,step6,step7,?_⟩
  simp [done,SourceSteps.deadFrame,f6,f5,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,f4,f3,
    SourceSteps.liveFrame,f2,f1,size,Array.getElem?_set,Array.getElem_set,resultRaw]
  rfl

#print axioms actual_seven_statements
end DuplicatePrefix.PointerAddBody
