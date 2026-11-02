import duplicate_prefix.CurrentCallSourceArguments
import duplicate_prefix.CurrentCallPush

namespace DuplicatePrefix.CurrentCallSpatialEntryControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.DataStructures
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open TypedBorrowSteps ReferenceBorrowDriver ReturnProtection
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The actual argument scope followed by destination protection and frame finish.
The equations consumed below are internal products of the source and Bool producers. -/
def action (h : RootCallCore.RootHooks) (value : Immediate Provenance) (count : UInt64) (place : MPlaceTy Provenance) :
    MachineHooks.M MiriMemoryKind Machine.RootUser Unit := do
  let _ ← h.withRetagMode () .FnEntry (RootCallCore.argumentBody h ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second count))
  RootEntryTail.tail h place

theorem finish_of_arguments (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (rawLocals : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (borrowFrame : FrameState) (pointer : Pointer Provenance) (len count : UInt64) (sourceId : AllocId) (sourceTag : BorTag)
    (before sourceMachine finalMachine : Before) (sourceFrame : FrameState) (boolId : AllocId) (boolTag : BorTag)
    (place : MPlaceTy Provenance)
    (arguments : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent frames root.frame before)=.ok (2,2) (Storage.withCurrent frames
        (RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count).frame sourceMachine))
    (protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan (RootArgumentsTwo.result
        (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame sourceMachine)=
      .ok () (Storage.withCurrent frames (registeredFrame (atSpan (RootArgumentsTwo.result
        (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame sourceFrame boolId boolTag) finalMachine)) :
    action (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
      (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm count place
      (Storage.withCurrent frames root.frame before)=
      .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
        {registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame
          sourceFrame boolId boolTag with location:=.unwinding ⟨559⟩}) finalMachine) ∧
    RootEntryTail.tail (ExecutionMachine.callHooks (config options (remaining+1) span) limits) place
      (Storage.withCurrent frames (RootArgumentsTwo.result
        (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count).frame sourceMachine)=
      .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
        {registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame
          sourceFrame boolId boolTag with location:=.unwinding ⟨559⟩}) finalMachine) := by
  let argsRoot := RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count
  let protectedFrame := registeredFrame (atSpan argsRoot ⟨601⟩).frame sourceFrame boolId boolTag
  have dead : ∀ slot : Fin 25,slot.val≠1 → slot.val≠2 →
      (protectedFrame.locals[slot.val]'(by simpa only [protectedFrame,registeredFrame,TypedRetagEntry.frameWithBorrow,atSpan] using argsRoot.valid slot)).value=.dead := by
    intro slot ne1 ne2
    have found := CurrentCallSourceArguments.result_other_local options remaining span root borrowFrame pointer len count sourceId sourceTag slot.val ne1 ne2
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


/-- The real raw push and call preamble consume the already derived actual
argument result and protection tail. No allocation, completion, or ownership shape is
introduced by this control step. -/
def root (before : Before) (frames : Array CompilerFrameContext.ActualFrame)
    (place : MPlaceTy Provenance) (race : before.dataRace=none) : RootFrame :=
  RootFrameData.raw (CurrentCallPush.preparedMachine before frames) (.memory place)
    (CallEntryFacts.freshRoot before).2 race

theorem init_of_steps (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (frames : Array CompilerFrameContext.ActualFrame)
    (place : MPlaceTy Provenance) (race : before.dataRace=none)
    (debug : options.place.debugAssertions=false)
    (ready : CurrentCallPush.StackReadiness before frames)
    (value : Immediate Provenance) (count : UInt64) (after : RootState)
    (argsRoot : RootFrame) (sourceMachine : Before)
    (arguments : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate value,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent frames (root before frames place race).frame (CurrentCallPush.preparedMachine before frames))=
      .ok (2,2) (Storage.withCurrent frames argsRoot.frame sourceMachine))
    (tail : RootEntryTail.tail (ExecutionMachine.callHooks (config options (remaining+1) span) limits) place
      (Storage.withCurrent frames argsRoot.frame sourceMachine)=.ok () after) :
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate value,ActualReferenceMetadata.reference⟩,.Copy (second count)]
      false (.memory place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState)=.ok () after := by
  let initialRoot := root before frames place race
  let machine := CurrentCallPush.preparedMachine before frames
  have push := CurrentCallPush.push options (remaining+1) span limits debug before frames (.memory place) ready
  have rawEq : CallEntryFacts.rawPushedState frames before (.memory place)=Storage.withCurrent frames initialRoot.frame machine := rfl
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span frames initialRoot.frame machine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span frames initialRoot.frame initialRoot.frame machine
  have preamble : initialRoot.frame.location=.unwinding ⟨559⟩ := rfl
  have trackNone : initialRoot.frame.trackCallerArg=none := rfl
  have unchanged : {initialRoot.frame with trackCallerArg:=none}=initialRoot.frame := by rw [←trackNone]
  rw [RootCallCore.actual_entry_eq]
  unfold RootCallCore.core
  simp only [bind,EStateM.bind]
  rw [push,rawEq]
  dsimp only
  rw [getFrame]
  simp only [EStateM.bind,preamble,pure,EStateM.pure]
  simp only [preamble] at unchanged
  rw [unchanged,setFrame]
  dsimp only
  erw [arguments]
  dsimp only
  exact tail

/-- The exact source-copy and Bool-protection equations drive the complete real
root initialization, including raw push, mode scope, and frame finish. This is
a lower composition lemma; its operation equations are derived by the paired
spatial producer, rather than assumed by ordinary admission. -/
theorem init_of_arguments (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (rawLocals : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (borrowFrame : FrameState) (pointer : Pointer Provenance) (len count : UInt64) (sourceId : AllocId) (sourceTag : BorTag)
    (before sourceMachine finalMachine : Before) (sourceFrame : FrameState) (boolId : AllocId) (boolTag : BorTag)
    (place : MPlaceTy Provenance)
    (arguments : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent frames root.frame before)=.ok (2,2) (Storage.withCurrent frames
        (RootArgumentsTwo.result (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count).frame sourceMachine))
    (initial : Before) (race : initial.dataRace=none)
    (debug : options.place.debugAssertions=false)
    (stackReady : CurrentCallPush.StackReadiness initial frames)
    (rootEq : root=CurrentCallSpatialEntryControl.root initial frames place race)
    (preparedEq : before=CurrentCallPush.preparedMachine initial frames)
    (protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan (RootArgumentsTwo.result
        (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame sourceMachine)=
      .ok () (Storage.withCurrent frames (registeredFrame (atSpan (RootArgumentsTwo.result
        (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame sourceFrame boolId boolTag) finalMachine)) :
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩,
        .Copy (second count)] false (.memory place) (.stop true) (⟨⟨frames⟩,initial⟩ : RootState)=
      .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
        {registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame
          sourceFrame boolId boolTag with location:=.unwinding ⟨559⟩}) finalMachine) := by
  obtain ⟨_,tail⟩ := finish_of_arguments options limits remaining span frames root rawLocals
    borrowFrame pointer len count sourceId sourceTag before sourceMachine finalMachine sourceFrame boolId boolTag
    place arguments protection
  subst root
  subst before
  exact init_of_steps options limits remaining span initial frames place race debug stackReady
    (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm count _ _ sourceMachine arguments tail

/-- The actual source copy is consumed once; the usize argument and enclosing
FnEntry mode scope are derived internally before the Bool protection and real
root initialization. This lower step has no source-wide ancestry witness. -/
theorem init_of_copy_protect (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (rawLocals : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (borrowFrame : FrameState) (pointer : Pointer Provenance) (len count : UInt64) (sourceId : AllocId) (sourceTag : BorTag)
    (before sourceMachine finalMachine : Before) (sourceFrame : FrameState) (boolId : AllocId) (boolTag : BorTag)
    (place : MPlaceTy Provenance)
    (tracker nextTracker : MachineHooks.BorrowState) (sourceFnMachine : Before)
    (tracked : before.borrowTracker=some tracker)
    (afterTracked : sourceFnMachine.borrowTracker=some nextTracker)
    (ghost : before.user.payload.ghost=false) (shallow : before.user.payload.validation=.Shallow)
    (afterGhost : sourceFnMachine.user.payload.ghost=false)
    (afterShallow : sourceFnMachine.user.payload.validation=.Shallow)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (sourceMachineEq : sourceMachine={sourceFnMachine with borrowTracker:=some {nextTracker with retagMode:=tracker.retagMode}})
    (copy : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames (firstLive root).frame (ScopedFrame.entered before tracker .FnEntry))=
      .ok () (Storage.withCurrent frames (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag).frame sourceFnMachine))
    (initial : Before) (race : initial.dataRace=none)
    (debug : options.place.debugAssertions=false)
    (stackReady : CurrentCallPush.StackReadiness initial frames)
    (rootEq : root=CurrentCallSpatialEntryControl.root initial frames place race)
    (preparedEq : before=CurrentCallPush.preparedMachine initial frames)
    (protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan (RootArgumentsTwo.result
        (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame sourceMachine)=
      .ok () (Storage.withCurrent frames (registeredFrame (atSpan (RootArgumentsTwo.result
        (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame sourceFrame boolId boolTag) finalMachine)) :
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩,
        .Copy (second count)] false (.memory place) (.stop true) (⟨⟨frames⟩,initial⟩ : RootState)=
      .ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
        {registeredFrame (atSpan (RootArgumentsTwo.result
          (CurrentCallSourceArguments.doneRoot options remaining span root borrowFrame pointer len sourceId sourceTag) count) ⟨601⟩).frame
          sourceFrame boolId boolTag with location:=.unwinding ⟨559⟩}) finalMachine) := by
  have arguments := (CurrentCallSourceArguments.arguments options limits remaining span debug fuel fuelEq
    frames root rawLocals before sourceFnMachine tracker nextTracker tracked afterTracked ghost shallow
    afterGhost afterShallow borrowFrame pointer len count sourceId sourceTag copy).2
  rw [←sourceMachineEq] at arguments
  exact init_of_arguments options limits remaining span frames root rawLocals borrowFrame pointer len count
    sourceId sourceTag before sourceMachine finalMachine sourceFrame boolId boolTag place arguments
    initial race debug stackReady rootEq preparedEq protection

end
end DuplicatePrefix.CurrentCallSpatialEntryControl
open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallSpatialEntryControl" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved spatial entry control dependency {dependency}"
