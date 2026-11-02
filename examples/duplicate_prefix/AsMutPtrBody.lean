import duplicate_prefix.AsMutPtrRawAssign
import duplicate_prefix.AsMutPtrCastAssign
import duplicate_prefix.AsMutPtrLocalCopy
import duplicate_prefix.AsMutPtrStorage
import duplicate_prefix.AsMutPtrFrame
import duplicate_prefix.TraceComposition
namespace DuplicatePrefix.AsMutPtrBody
noncomputable section
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open AsMutPtrFacts
set_option maxRecDepth 65536
set_option maxHeartbeats 24000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem actual_steps
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (len : UInt64)
    (carrierValid : AsMutPtrCarrier.Valid machine (.inl pointer) len)
    (size : frame.locals.size = 5)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (PtrMetadataComplete.rawImmediate (.inl pointer)
        (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : (frame.locals[1]'(by omega)).layout = some ActualReferenceMetadata.reference)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead)
    (uncached2 : (frame.locals[2]'(by omega)).layout = none)
    (dead3 : (frame.locals[3]'(by omega)).value = .dead)
    (uncached3 : (frame.locals[3]'(by omega)).layout = none)
    (dead4 : (frame.locals[4]'(by omega)).value = .dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout = none)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    ∃ s1 s2 s3 s4 s5 s6 s7 s8 s9 : CanonicalConfigFacts.RootState, ∃ done : CompilerFrameContext.ActualFrame,
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () (Storage.withCurrent frames frame machine) = (s1,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () s1 = (s2,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () s2 = (s3,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () s3 = (s4,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () s4 = (s5,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () s5 = (s6,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () s6 = (s7,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () s7 = (s8,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () s8 = (s9,.ok true) ∧
      ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () s9 = (Storage.withCurrent frames done machine,.ok true) ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧
      done.functionInstance = frame.functionInstance ∧ done.extra = frame.extra ∧
      done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧
      done.locals[1]? = frame.locals[1]? ∧ done.locals.size = 5 ∧ done.location = .mir ⟨0,10⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base pointer))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      (done.locals[2]?.map (·.value)) = some .dead ∧
      (done.locals[3]?.map (·.value)) = some .dead ∧
      (done.locals[4]?.map (·.value)) = some .dead := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  have target : config.access.runtime.base = (PreparedContracts.actualConfig options () remaining span).access.runtime.base := by
    rw [CanonicalConfigFacts.actual_access_runtime options () (remaining+1) span,
      CanonicalConfigFacts.actual_access_runtime options () remaining span]
  let value := PtrMetadataComplete.rawImmediate (.inl pointer) config.access.runtime.base len
  let thin := Immediate.scalar (Scalar.fromPointer config.access.runtime.base pointer)
  obtain ⟨s1,s2,s3,step1,step2,step3,third,_,_⟩ := AsMutPtrStorage.actual_initial_storage
    options (remaining+1) span limits frames frame machine body location size dead2 dead3 dead4 noClocks
  let f3 := AsMutPtrFrame.entered frame size
  rw [third,AsMutPtrFrame.after_storage frame size uncached2 uncached3 uncached4] at step3
  have size3 : f3.locals.size = 5 := by simp [f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,size]
  have v31 : (1 : Miri.MIR.LocalId) < f3.locals.size := by rw [size3];decide
  have v34 : (4 : Miri.MIR.LocalId) < f3.locals.size := by rw [size3];decide
  let block := HelperCompilerFacts.asMutPtrBody.body.basicBlocks[0]'(by with_unfolding_all decide +kernel)
  have blockAt : HelperCompilerFacts.asMutPtrBody.body.basicBlocks[0]? = some block := by simp [block]
  have raw := AsMutPtrRawAssign.actual_raw_assignment options limits remaining span debugOff fuel validationFuel
    frames f3 machine (.inl pointer) len carrierValid v31 v34
    (by simpa [f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set] using live1) (by simpa [f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set] using cached1) (by simp [f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set]) (by simpa [f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set] using uncached4)
    body identity callee noClocks ghost shallow dynamicFuel dynamicEq cmp metadata notConstructed
  let rawFrame := AsMutPtrRawAssign.copied4 f3 v34 (PtrMetadataComplete.rawImmediate (.inl pointer)
    (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)
  let f4 := {rawFrame with location := .mir ⟨0,4⟩}
  have step4 := SourceSteps.assign_exact config limits () frames f3 rawFrame machine machine ⟨0,3⟩ block
    (block.statements[3]'(by with_unfolding_all decide +kernel)) ⟨4,#[]⟩ (.RawPtr .Mut ⟨1,#[.Deref]⟩)
    rfl (by change frame.body.basicBlocks[0]? = _;rw [body];exact blockAt)
    (by simp) (by with_unfolding_all rfl) raw rfl
  have size4 : f4.locals.size = 5 := (by simp [f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,size])
  have v44 : (4 : Miri.MIR.LocalId) < f4.locals.size := by rw [size4];decide
  have v43 : (3 : Miri.MIR.LocalId) < f4.locals.size := by rw [size4];decide
  have q3 := AsMutPtrLayouts.compute frames f4 machine body identity callee 3 (Or.inr (Or.inr (Or.inl rfl)))
  have copy3 := AsMutPtrLocalCopy.mut_slice options limits remaining span debugOff fuel validationFuel
    frames f4 machine 4 3 pointer len (by decide) v44 v43
    (by simp [f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,target]) (by simp [f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set]) (by simp [f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set]) (by simpa [f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set] using uncached3)
    (by simpa using q3) noClocks tracker tracked defaultMode ghost shallow
  let copied3 := ActualLocalCopy.written f4 3 rawLayout v43
    (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len rawLayout).imm
  let f5 := {copied3 with location := .mir ⟨0,5⟩}
  have step5 := SourceSteps.assign_exact config limits () frames f4 copied3 machine machine ⟨0,4⟩ block
    (block.statements[4]'(by with_unfolding_all decide +kernel)) ⟨3,#[]⟩ (.Use (.Copy ⟨4,#[]⟩) .Yes)
    rfl (by change frame.body.basicBlocks[0]? = _;rw [body];exact blockAt)
    (by simp) (by with_unfolding_all rfl) copy3 rfl
  have size5 : f5.locals.size = 5 := (by simp [f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,size])
  have v52 : (2 : Miri.MIR.LocalId) < f5.locals.size := by rw [size5];decide
  have v53 : (3 : Miri.MIR.LocalId) < f5.locals.size := by rw [size5];decide
  have cast := AsMutPtrCastAssign.actual_cast_assignment options limits remaining span debugOff fuel validationFuel
    frames f5 machine pointer len v52 v53
    (by simp [f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set]) (by simpa [f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set] using uncached2) (by simp [f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,config,target]) (by simp [f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set])
    body identity callee rfl noClocks ghost shallow
  let casted := ActualLocalCopy.written f5 2 CopyCompilerFacts.destPointerLayout v52 thin
  let f6 := {casted with location := .mir ⟨0,6⟩}
  have step6 := SourceSteps.assign_exact config limits () frames f5 casted machine machine ⟨0,5⟩ block
    (block.statements[5]'(by with_unfolding_all decide +kernel)) ⟨2,#[]⟩ (.Cast .PtrToPtr (.Move ⟨3,#[]⟩) 8)
    rfl (by change frame.body.basicBlocks[0]? = _;rw [body];exact blockAt)
    (by simp) (by with_unfolding_all rfl) cast rfl
  have size6 : f6.locals.size = 5 := (by simp [f6,casted,f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,size])
  have v62 : (2 : Miri.MIR.LocalId) < f6.locals.size := by rw [size6];decide
  have v60 : (0 : Miri.MIR.LocalId) < f6.locals.size := by rw [size6];decide
  have q0 := AsMutPtrLayouts.compute frames f6 machine body identity callee 0 (Or.inl rfl)
  have copy0 := ScalarLocalCopy.pointer options limits remaining span debugOff fuel validationFuel
    frames f6 machine 2 0 (Scalar.fromPointer config.access.runtime.base pointer) (by decide) v62 v60
    (by simp [f6,casted,f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,thin]) (by simp [f6,casted,f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set]) (by simpa [f6,casted,f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set] using live0) (by simpa [f6,casted,f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set] using uncached0)
    (by simpa using q0) noClocks tracker tracked defaultMode ghost shallow
  let returned := ActualLocalCopy.written f6 0 CopyCompilerFacts.destPointerLayout v60 thin
  let f7 := {returned with location := .mir ⟨0,7⟩}
  have step7 := SourceSteps.assign_exact config limits () frames f6 returned machine machine ⟨0,6⟩ block
    (block.statements[6]'(by with_unfolding_all decide +kernel)) ⟨0,#[]⟩ (.Use (.Copy ⟨2,#[]⟩) .Yes)
    rfl (by change frame.body.basicBlocks[0]? = _;rw [body];exact blockAt)
    (by simp) (by with_unfolding_all rfl) copy0 rfl
  have size7 : f7.locals.size = 5 := (by simp [f7,returned,f6,casted,f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,size])
  have v74 : (4 : Miri.MIR.LocalId) < f7.locals.size := by rw [size7];decide
  let f8 := SourceSteps.deadFrame f7 ⟨0,7⟩ 4 v74
  have step8 := SourceSteps.storage_dead_exact config limits () frames f7 machine ⟨0,7⟩ block
    (block.statements[7]'(by with_unfolding_all decide +kernel)) 4 (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len rawLayout).imm rfl
    (by change frame.body.basicBlocks[0]? = _;rw [body];exact blockAt)
    (by simp) (by with_unfolding_all rfl) v74 (by decide)
    (by simp [f7,returned,f6,casted,f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,thin,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,target])
  have size8 : f8.locals.size = 5 := (by simp [f8,f7,returned,f6,casted,f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,size])
  have v83 : (3 : Miri.MIR.LocalId) < f8.locals.size := by rw [size8];decide
  let f9 := SourceSteps.deadFrame f8 ⟨0,8⟩ 3 v83
  have step9 := SourceSteps.storage_dead_exact config limits () frames f8 machine ⟨0,8⟩ block
    (block.statements[8]'(by with_unfolding_all decide +kernel)) 3 (RetagReferencePlace.sliceValue (PreparedContracts.actualConfig options () remaining span).access.runtime.base pointer len rawLayout).imm rfl
    (by change frame.body.basicBlocks[0]? = _;rw [body];exact blockAt)
    (by simp) (by with_unfolding_all rfl) v83 (by decide)
    (by simp [f8,f7,returned,f6,casted,f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,thin,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,target])
  have size9 : f9.locals.size = 5 := (by simp [f9,f8,f7,returned,f6,casted,f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,size])
  have v92 : (2 : Miri.MIR.LocalId) < f9.locals.size := by rw [size9];decide
  let done := SourceSteps.deadFrame f9 ⟨0,9⟩ 2 v92
  have step10 := SourceSteps.storage_dead_exact config limits () frames f9 machine ⟨0,9⟩ block
    (block.statements[9]'(by with_unfolding_all decide +kernel)) 2 thin rfl
    (by change frame.body.basicBlocks[0]? = _;rw [body];exact blockAt)
    (by simp) (by with_unfolding_all rfl) v92 (by decide)
    (by simp [f9,f8,f7,returned,f6,casted,f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,thin,PtrMetadataComplete.rawImmediate,RetagReferencePlace.sliceValue,target])
  refine ⟨s1,s2,Storage.withCurrent frames f3 machine,Storage.withCurrent frames f4 machine,
    Storage.withCurrent frames f5 machine,Storage.withCurrent frames f6 machine,Storage.withCurrent frames f7 machine,
    Storage.withCurrent frames f8 machine,Storage.withCurrent frames f9 machine,done,
    step1,step2,step3,step4,step5,step6,step7,step8,step9,step10,?_⟩
  simp [done,f9,f8,f7,returned,f6,casted,f5,copied3,f4,rawFrame,f3,AsMutPtrFrame.entered,SourceSteps.liveFrame,SourceSteps.deadFrame,ActualLocalCopy.written,LocalPlaces.cachePlaceLayout,AsMutPtrRawAssign.copied4,AsMutPtrRawAssign.cached4,PtrMetadataExecution.writeFrame,Array.getElem_set,size,thin,Array.getElem?_eq_getElem,Array.getElem_set]
  rfl

theorem actual_ten_statements
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions = false) (fuel : Nat)
    (validationFuel : options.limits.validation = fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (pointer : Pointer Provenance) (len : UInt64)
    (carrierValid : AsMutPtrCarrier.Valid machine (.inl pointer) len)
    (size : frame.locals.size = 5)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (live1 : (frame.locals[1]'(by omega)).value = .live (.immediate
      (PtrMetadataComplete.rawImmediate (.inl pointer)
        (PreparedContracts.actualConfig options () remaining span).access.runtime.base len)))
    (cached1 : (frame.locals[1]'(by omega)).layout = some ActualReferenceMetadata.reference)
    (dead2 : (frame.locals[2]'(by omega)).value = .dead)
    (uncached2 : (frame.locals[2]'(by omega)).layout = none)
    (dead3 : (frame.locals[3]'(by omega)).value = .dead)
    (uncached3 : (frame.locals[3]'(by omega)).layout = none)
    (dead4 : (frame.locals[4]'(by omega)).value = .dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout = none)
    (body : frame.body = HelperCompilerFacts.asMutPtrBody.body)
    (identity : frame.bodyIdentity = HelperCompilerFacts.asMutPtrBody.identity)
    (callee : frame.functionInstance = HelperCompilerFacts.asMutPtrCall.callee)
    (location : frame.location = .mir ⟨0,0⟩)
    (noClocks : frame.extra.dataRace = none)
    (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker = some tracker)
    (defaultMode : tracker.retagMode = .Default)
    (ghost : machine.user.payload.ghost = false)
    (shallow : machine.user.payload.validation = .Shallow)
    (dynamicFuel : Nat) (dynamicEq : options.place.dynamicFuel = dynamicFuel+1)
    (cmp : ProjectionMetadataFacts.NullComparator)
    (metadata : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).metadata = PreparedReflection.actual.runtime)
    (notConstructed : (EvalProjectionMachine.arrays.get (Storage.withCurrent frames frame machine)).entries.any (·.value.ty == 4) = false) :
    ∃ done : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits (Storage.withCurrent frames frame machine) (Storage.withCurrent frames done machine) ∧
      done.body = frame.body ∧ done.bodyIdentity = frame.bodyIdentity ∧
      done.functionInstance = frame.functionInstance ∧ done.extra = frame.extra ∧
      done.returnPlace = frame.returnPlace ∧ done.returnContinuation = frame.returnContinuation ∧
      done.vaList = frame.vaList ∧ done.localsIdentity = frame.localsIdentity ∧
      done.locals[1]? = frame.locals[1]? ∧ done.locals.size = 5 ∧ done.location = .mir ⟨0,10⟩ ∧
      done.locals[0]? = some ⟨.live (.immediate (.scalar (Scalar.fromPointer (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base pointer))),some CopyCompilerFacts.destPointerLayout⟩ ∧
      (done.locals[2]?.map (·.value)) = some .dead ∧
      (done.locals[3]?.map (·.value)) = some .dead ∧
      (done.locals[4]?.map (·.value)) = some .dead := by
  obtain ⟨s1,s2,s3,s4,s5,s6,s7,s8,s9,done,e1,e2,e3,e4,e5,e6,e7,e8,e9,e10,properties⟩ := actual_steps
    options limits remaining span debugOff fuel validationFuel frames frame machine pointer len carrierValid
    size live0 uncached0 live1 cached1 dead2 uncached2 dead3 uncached3 dead4 uncached4 body identity callee location
    noClocks tracker tracked defaultMode ghost shallow dynamicFuel dynamicEq cmp metadata notConstructed
  exact ⟨done,TraceComposition.ten e1 e2 e3 e4 e5 e6 e7 e8 e9 e10,properties⟩

#print axioms actual_steps
#print axioms actual_ten_statements
end
end DuplicatePrefix.AsMutPtrBody
