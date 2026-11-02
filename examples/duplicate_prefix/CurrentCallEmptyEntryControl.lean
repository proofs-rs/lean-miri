import duplicate_prefix.CurrentCallEmptySourceArguments

/-! Pure root entry control for the ACTUAL empty argument encoding, including
integer slices. Lower actual copy/protection equations are consumed internally;
no pointer reinterpretation or source ownership is introduced. -/
namespace DuplicatePrefix.CurrentCallEmptyEntryControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection CurrentCallEmptyTypedEntry
open CurrentCallSpatialEntryControl
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def value (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (argument : DuplicatePrefixSliceArgument.Argument) :=
  DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base argument 0 ActualReferenceMetadata.reference

private theorem other_local {options before tracker argument}
    (effect : Effect options before tracker argument) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root : RootFrame) (borrowFrame : FrameState) (count : UInt64) (slot : Nat) (ne1 : slot≠1) (ne2 : slot≠2) :
    (RootArgumentsTwo.result (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count).frame.locals[slot]?=
      root.frame.locals[slot]? := by
  cases effect <;>
    simp only [RootArgumentsTwo.result,CurrentCallEmptySourceArguments.doneRoot,resultFrame,Effect.allocation,registered,copied,
      CurrentCallEmptyReferenceValidation.writtenFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,
      firstLive,firstCache,RootFrameData.write,RootFrameData.live,RootFrameData.cache,RootFrameData.atSpan,
      LocalOperands.cachedLayoutFrame,Array.getElem?_set,Ne.symm ne1,Ne.symm ne2,ite_false,i1,i2]

theorem finish_of_arguments (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (rawLocals : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (effect : Effect options before tracker argument) (borrowFrame : FrameState) (count : UInt64)
    (sourceMachine finalMachine : Before) (sourceFrame : FrameState) (boolId : AllocId) (boolTag : BorTag)
    (place : MPlaceTy Provenance)
    (arguments : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate (value options remaining span argument).imm,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent frames root.frame before)=.ok (2,2) (Storage.withCurrent frames
        (RootArgumentsTwo.result (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count).frame sourceMachine))
    (protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan (RootArgumentsTwo.result
        (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count) ⟨601⟩).frame sourceMachine)=
      .ok () (Storage.withCurrent frames (registeredFrame (atSpan (RootArgumentsTwo.result
        (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count) ⟨601⟩).frame sourceFrame boolId boolTag) finalMachine)) :
    action (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
      (value options remaining span argument).imm count place
      (Storage.withCurrent frames root.frame before)=
      .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
        {registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count) ⟨601⟩).frame
          sourceFrame boolId boolTag with location:=.unwinding ⟨559⟩}) finalMachine) ∧
    RootEntryTail.tail (ExecutionMachine.callHooks (config options (remaining+1) span) limits) place
      (Storage.withCurrent frames (RootArgumentsTwo.result
        (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count).frame sourceMachine)=
      .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
        {registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count) ⟨601⟩).frame
          sourceFrame boolId boolTag with location:=.unwinding ⟨559⟩}) finalMachine) := by
  let argsRoot := RootArgumentsTwo.result (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count
  let protectedFrame := registeredFrame (atSpan argsRoot ⟨601⟩).frame sourceFrame boolId boolTag
  have dead : ∀ slot : Fin 25,slot.val≠1 → slot.val≠2 →
      (protectedFrame.locals[slot.val]'(by simpa only [protectedFrame,registeredFrame,TypedRetagEntry.frameWithBorrow,atSpan] using argsRoot.valid slot)).value=.dead := by
    intro slot ne1 ne2
    have found := other_local effect remaining span root borrowFrame count slot.val ne1 ne2
    rw [rawLocals] at found
    have raw : (Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))[slot.val]?=some ⟨.dead,none⟩ := by simp [slot.isLt]
    have cell : argsRoot.frame.locals[slot.val]?=some ⟨.dead,none⟩ := found.trans raw
    have exactCell := Option.some.inj ((Array.getElem?_eq_getElem (argsRoot.valid slot)).symm.trans cell)
    exact congrArg LocalState.value exactCell
  have finish := RootEntryFinish.actual_finish options limits (remaining+1) span frames protectedFrame finalMachine
    argsRoot.body argsRoot.size (dead ⟨0,by decide⟩ (by decide) (by decide)) (dead ⟨6,by decide⟩ (by decide) (by decide))
    (dead ⟨13,by decide⟩ (by decide) (by decide)) (dead ⟨14,by decide⟩ (by decide) (by decide)) argsRoot.noClocks
  have tail := CurrentCallSourceArguments.tail_of_steps options limits (remaining+1) span frames argsRoot sourceMachine place _ _ protection finish
  refine ⟨?_,tail⟩
  unfold action
  simp only [bind,EStateM.bind]
  rw [arguments]
  exact tail


theorem init_of_arguments (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (rawLocals : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (effect : Effect options before tracker argument) (borrowFrame : FrameState) (count : UInt64)
    (sourceMachine finalMachine : Before) (sourceFrame : FrameState) (boolId : AllocId) (boolTag : BorTag)
    (place : MPlaceTy Provenance)
    (arguments : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate (value options remaining span argument).imm,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent frames root.frame before)=.ok (2,2) (Storage.withCurrent frames
        (RootArgumentsTwo.result (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count).frame sourceMachine))
    (initial : Before) (race : initial.dataRace=none)
    (debug : options.place.debugAssertions=false)
    (stackReady : CurrentCallPush.StackReadiness initial frames)
    (rootEq : root=CurrentCallSpatialEntryControl.root initial frames place race)
    (preparedEq : before=CurrentCallPush.preparedMachine initial frames)
    (protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan (RootArgumentsTwo.result
        (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count) ⟨601⟩).frame sourceMachine)=
      .ok () (Storage.withCurrent frames (registeredFrame (atSpan (RootArgumentsTwo.result
        (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count) ⟨601⟩).frame sourceFrame boolId boolTag) finalMachine)) :
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (value options remaining span argument).imm,ActualReferenceMetadata.reference⟩,
        .Copy (second count)] false (.memory place) (.stop true) (⟨⟨frames⟩,initial⟩ : RootState)=
      .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
        {registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count) ⟨601⟩).frame
          sourceFrame boolId boolTag with location:=.unwinding ⟨559⟩}) finalMachine) := by
  obtain ⟨_,tail⟩ := finish_of_arguments options limits remaining span frames root rawLocals
    before tracker argument effect borrowFrame count sourceMachine finalMachine sourceFrame boolId boolTag
    place arguments protection
  subst root
  subst before
  exact init_of_steps options limits remaining span initial frames place race debug stackReady
    (value options remaining span argument).imm count _ _ sourceMachine arguments tail

/-- The actual source copy is consumed once; the usize argument and enclosing
FnEntry mode scope are derived internally before the Bool protection and real
root initialization. This lower step has no source-wide ancestry witness. -/
theorem init_of_copy_protect (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (rawLocals : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (effect : Effect options before tracker argument) (borrowFrame : FrameState) (count : UInt64)
    (sourceMachine finalMachine : Before) (sourceFrame : FrameState) (boolId : AllocId) (boolTag : BorTag)
    (place : MPlaceTy Provenance)
    (nextTracker : MachineHooks.BorrowState) (sourceFnMachine : Before)
    (tracked : before.borrowTracker=some tracker)
    (afterTracked : sourceFnMachine.borrowTracker=some nextTracker)
    (ghost : before.user.payload.ghost=false) (shallow : before.user.payload.validation=.Shallow)
    (afterGhost : sourceFnMachine.user.payload.ghost=false)
    (afterShallow : sourceFnMachine.user.payload.validation=.Shallow)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (sourceMachineEq : sourceMachine={sourceFnMachine with borrowTracker:=some {nextTracker with retagMode:=tracker.retagMode}})
    (copy : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (value options remaining span argument).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames (firstLive root).frame (ScopedFrame.entered before tracker .FnEntry))=
      .ok () (Storage.withCurrent frames (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame).frame sourceFnMachine))
    (initial : Before) (race : initial.dataRace=none)
    (debug : options.place.debugAssertions=false)
    (stackReady : CurrentCallPush.StackReadiness initial frames)
    (rootEq : root=CurrentCallSpatialEntryControl.root initial frames place race)
    (preparedEq : before=CurrentCallPush.preparedMachine initial frames)
    (protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan (RootArgumentsTwo.result
        (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count) ⟨601⟩).frame sourceMachine)=
      .ok () (Storage.withCurrent frames (registeredFrame (atSpan (RootArgumentsTwo.result
        (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count) ⟨601⟩).frame sourceFrame boolId boolTag) finalMachine)) :
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (value options remaining span argument).imm,ActualReferenceMetadata.reference⟩,
        .Copy (second count)] false (.memory place) (.stop true) (⟨⟨frames⟩,initial⟩ : RootState)=
      .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
        {registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallEmptySourceArguments.doneRoot effect remaining span root borrowFrame) count) ⟨601⟩).frame
          sourceFrame boolId boolTag with location:=.unwinding ⟨559⟩}) finalMachine) := by
  have arguments := (CurrentCallEmptySourceArguments.arguments options limits remaining span debug fuel fuelEq
    frames root rawLocals before sourceFnMachine tracker nextTracker tracked afterTracked ghost shallow
    afterGhost afterShallow argument effect borrowFrame count copy).2
  rw [←sourceMachineEq] at arguments
  exact init_of_arguments options limits remaining span frames root rawLocals before tracker argument effect borrowFrame count
    sourceMachine finalMachine sourceFrame boolId boolTag place arguments
    initial race debug stackReady rootEq preparedEq protection

end
end DuplicatePrefix.CurrentCallEmptyEntryControl
