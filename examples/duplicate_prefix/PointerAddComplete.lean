import duplicate_prefix.PointerAddReturn
namespace DuplicatePrefix.PointerAddComplete
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Concurrency
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def isDirect : LocalValue Provenance → Bool
  | .dead | .live (.immediate _) => true
  | .live (.indirect _) => false

theorem all_direct_five (slots : Array (LocalState Provenance LocalLayout))
    (size : slots.size = 5)
    (zero : slots[0]?.map (fun slot => isDirect slot.value) = some true)
    (one : slots[1]?.map (fun slot => isDirect slot.value) = some true)
    (two : slots[2]?.map (fun slot => isDirect slot.value) = some true)
    (three : slots[3]?.map (fun slot => isDirect slot.value) = some true)
    (four : slots[4]?.map (fun slot => isDirect slot.value) = some true) :
    ∀ slot ∈ slots, ∀ memory, slot.value ≠ .live (.indirect memory) := by
  intro slot member memory bad
  rcases Array.mem_iff_getElem.mp member with ⟨index,valid,equal⟩
  have cases5 : index = 0 ∨ index = 1 ∨ index = 2 ∨ index = 3 ∨ index = 4 := by omega
  have flag : isDirect slot.value = true := by
    rcases cases5 with rfl | rfl | rfl | rfl | rfl
    · simpa [Array.getElem?_eq_getElem valid,equal] using zero
    · simpa [Array.getElem?_eq_getElem valid,equal] using one
    · simpa [Array.getElem?_eq_getElem valid,equal] using two
    · simpa [Array.getElem?_eq_getElem valid,equal] using three
    · simpa [Array.getElem?_eq_getElem valid,equal] using four
  rw [bad] at flag
  cases flag

theorem body_returns_offset
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller frame : CompilerFrameContext.ActualFrame)
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
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (callerId : Miri.MIR.LocalId) (callerValid : callerId < caller.locals.size)
    (callerLive : caller.locals[callerId].value = .live (.immediate .uninit))
    (callerCached : caller.locals[callerId].layout = some CopyCompilerFacts.destPointerLayout)
    (callerClocks : caller.extra.dataRace = none)
    (destination : frame.returnPlace.toRuntimePlace = LocalPlaces.localRuntimePlace frames.size caller callerId CopyCompilerFacts.destPointerLayout)
    (target : BasicBlockId) (unwindAction : UnwindAction)
    (continuation : frame.returnContinuation = .goto (some target) unwindAction)
    (varargs : frame.vaList = #[])
    (borrowFrame : Miri.TreeBorrows.FrameState)
    (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (empty : borrowFrame.protectedTags = #[])
    (thread : ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let config := PreparedContracts.actualConfig options () (remaining+1) span
    ∃ f1 f2 f3 f4 f5 f6 done : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) frame machine) =
        (Storage.withCurrent (frames.push caller) f1 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) f1 machine) =
        (Storage.withCurrent (frames.push caller) f2 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) f2 machine) =
        (Storage.withCurrent (frames.push caller) f3 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) f3 machine) =
        (Storage.withCurrent (frames.push caller) f4 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) f4 machine) =
        (Storage.withCurrent (frames.push caller) f5 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) f5 machine) =
        (Storage.withCurrent (frames.push caller) f6 machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) f6 machine) =
        (Storage.withCurrent (frames.push caller) done machine,.ok true) ∧
      ExecutionMachine.step config limits () (Storage.withCurrent (frames.push caller) done machine) =
        (Storage.withCurrent frames
          {PointerAddReturn.writeFrame caller callerId (.scalar (Scalar.fromPointer config.access.runtime.base
            (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count))))) callerValid with location := .mir ⟨target,0⟩}
          (PointerAddReturn.poppedMachine frames caller done (PointerAddReturn.accountedMachine options remaining span machine)
            (thread.topUserRelevantFrame.getD (frames.push caller).size)),.ok true) ∧
      done.extra = frame.extra := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let value : Scalar Provenance := Scalar.fromPointer config.access.runtime.base
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count)))
  obtain ⟨f1,f2,f3,f4,f5,f6,done,step1,step2,step3,step4,step5,step6,step7,
    doneBody,doneIdentity,doneFn,doneExtra,doneReturn,doneCont,doneVa,doneLocalsIdentity,doneArg1,doneArg2,
    doneSize,doneLocation,done0,done3,done4⟩ := PointerAddBody.actual_seven_statements
      options limits remaining span debugOff fuel validationFuel (frames.push caller) frame machine
      id tag base offset count entry size live0 uncached0 live1 cached1 live2 cached2 dead3 uncached3 dead4 uncached4
      sourceBody identity callee location noClocks tracker tracked defaultMode ghostFalse shallow cached present positive fits bounds
  have doneValid0 : (0 : Miri.MIR.LocalId) < done.locals.size := by rw [doneSize];decide
  have valid1 : (1 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  have valid2 : (2 : Miri.MIR.LocalId) < frame.locals.size := by rw [size];decide
  have slot0 : done.locals[0] = ⟨.live (.immediate (.scalar value)),some CopyCompilerFacts.destPointerLayout⟩ := by
    simpa only [Array.getElem?_eq_getElem doneValid0,Option.some.injEq] using done0
  have direct := all_direct_five done.locals doneSize
    (by simp [done0,isDirect])
    (by rw [doneArg1,Array.getElem?_eq_getElem valid1];simp [live1,isDirect])
    (by rw [doneArg2,Array.getElem?_eq_getElem valid2];simp [live2,isDirect])
    (by simpa only [Option.map_map,Function.comp_def,Option.map_some,isDirect] using congrArg (Option.map isDirect) done3)
    (by simpa only [Option.map_map,Function.comp_def,Option.map_some,isDirect] using congrArg (Option.map isDirect) done4)
  have step8 := PointerAddReturn.return_step options limits remaining span debugOff fuel validationFuel
    frames caller done machine value callerId (by rw [doneBody];exact sourceBody) doneLocation doneValid0
    (by rw [slot0]) (by rw [slot0]) (by rw [doneExtra];exact noClocks)
    callerValid callerLive callerCached callerClocks (by rw [doneReturn];exact destination) target unwindAction
    (by rw [doneCont];exact continuation) direct (by rw [doneVa];exact varargs) tracker borrowFrame tracked
    (by rw [doneExtra];exact frameTracked) empty thread active unchecked noGc fixed ghostFalse shallow
  exact ⟨f1,f2,f3,f4,f5,f6,done,step1,step2,step3,step4,step5,step6,step7,step8,doneExtra⟩

#print axioms body_returns_offset
end
end DuplicatePrefix.PointerAddComplete
