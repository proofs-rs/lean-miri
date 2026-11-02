import duplicate_prefix.CurrentCallSpatialEntryControl
import duplicate_prefix.RootArgumentsTwo
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.RootZeroCompletePrefix
namespace DuplicatePrefix.CurrentCallEmptyProtocolControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

/-- Neutral actual source-copy frame. Only the returned immediate and the real
source protector ledger are installed. This does not require the old image
Effect's Supported restriction or any source family. -/
def sourceRoot (root : RootFrame) (updated : Immediate Provenance) (sourceFrame : FrameState) : RootFrame :=
  let copied:=write (firstLive root) i1 updated
  {copied with frame:=TypedRetagEntry.frameWithBorrow copied.frame sourceFrame}

private theorem other (root : RootFrame) (updated : Immediate Provenance) (sourceFrame : FrameState)
    (slot : Nat) (different : slot≠1) :
    (sourceRoot root updated sourceFrame).frame.locals[slot]?=root.frame.locals[slot]? := by
  simp only [sourceRoot,TypedRetagEntry.frameWithBorrow,firstLive,firstCache,live,write,cache,atSpan,
    LocalOperands.cachedLayoutFrame,Array.getElem?_set,Ne.symm different,ite_false,i1]

/-- One usize argument and one enclosing FnEntry scope consume the SAME real
source-copy equation, retaining its actual updated machine and global state. -/
theorem arguments (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions=false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (before after : Before) (tracker nextTracker : MachineHooks.BorrowState)
    (tracked : before.borrowTracker=some tracker) (afterTracked : after.borrowTracker=some nextTracker)
    (ghost : before.user.payload.ghost=false) (shallow : before.user.payload.validation=.Shallow)
    (afterGhost : after.user.payload.ghost=false) (afterShallow : after.user.payload.validation=.Shallow)
    (input updated : Immediate Provenance) (sourceFrame : FrameState) (count : UInt64)
    (copy : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate input,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames (firstLive root).frame (ScopedFrame.entered before tracker .FnEntry))=
      .ok () (Storage.withCurrent frames (sourceRoot root updated sourceFrame).frame after)) :
    (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate input,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent frames root.frame before)=
      .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result (sourceRoot root updated sourceFrame) count).frame
        {after with borrowTracker:=some {nextTracker with retagMode:=tracker.retagMode}}) := by
  have raw1 : (root.frame.locals[1]'(root.valid i1))=⟨.dead,none⟩ := by
    have found : root.frame.locals[1]?=some (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=by rw [raw];rfl
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i1)).symm.trans found)
  have next2 : (sourceRoot root updated sourceFrame).frame.locals[2]?=some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    rw [other root updated sourceFrame 2 (by decide),raw];rfl
  have entry2:=Option.some.inj ((Array.getElem?_eq_getElem ((sourceRoot root updated sourceFrame).valid i2)).symm.trans next2)
  have body:=RootArgumentsTwo.body options limits remaining span debug fuel fuelEq frames root (sourceRoot root updated sourceFrame)
    (ScopedFrame.entered before tracker .FnEntry) after input count (congrArg LocalState.value raw1) (congrArg LocalState.layout raw1)
    (congrArg LocalState.value entry2) (congrArg LocalState.layout entry2) ghost shallow afterGhost afterShallow copy
  exact ScopedFrame.changed_state _ (Storage.withCurrent frames root.frame before)
    (Storage.withCurrent frames (RootArgumentsTwo.result (sourceRoot root updated sourceFrame) count).frame after)
    tracker nextTracker .FnEntry (2,2) tracked afterTracked body

/-- Raw push, two ABI arguments, actual typed Bool protection and frame finish
are joined once for every source representation and materialization effect. -/
theorem init_of_arguments (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (initial : Before) (frames : Array CompilerFrameContext.ActualFrame) (place : MPlaceTy Provenance)
    (race : initial.dataRace=none) (debug : options.place.debugAssertions=false)
    (stackReady : CurrentCallPush.StackReadiness initial frames)
    (input updated : Immediate Provenance) (sourceFrame : FrameState) (count : UInt64)
    (sourceMachine finalMachine : Before) (boolId : AllocId) (boolTag : BorTag)
    (arguments : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate input,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent frames (CurrentCallSpatialEntryControl.root initial frames place race).frame (CurrentCallPush.preparedMachine initial frames))=
      .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result (sourceRoot (CurrentCallSpatialEntryControl.root initial frames place race) updated sourceFrame) count).frame sourceMachine))
    (protection : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan (RootArgumentsTwo.result (sourceRoot (CurrentCallSpatialEntryControl.root initial frames place race) updated sourceFrame) count) ⟨601⟩).frame sourceMachine)=
      .ok () (Storage.withCurrent frames (TypedBorrowSteps.registeredFrame
        (atSpan (RootArgumentsTwo.result (sourceRoot (CurrentCallSpatialEntryControl.root initial frames place race) updated sourceFrame) count) ⟨601⟩).frame sourceFrame boolId boolTag) finalMachine)) :
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy ⟨.immediate input,ActualReferenceMetadata.reference⟩,.Copy (second count)] false (.memory place) (.stop true)
      (⟨⟨frames⟩,initial⟩ : RootState)=.ok () (Storage.withCurrent frames (CallEntryFacts.doneRootFrame
        {TypedBorrowSteps.registeredFrame (atSpan (RootArgumentsTwo.result (sourceRoot (CurrentCallSpatialEntryControl.root initial frames place race) updated sourceFrame) count) ⟨601⟩).frame sourceFrame boolId boolTag
          with location:=.unwinding ⟨559⟩}) finalMachine) := by
  let root:=CurrentCallSpatialEntryControl.root initial frames place race
  let args:=RootArgumentsTwo.result (sourceRoot root updated sourceFrame) count
  let protectedFrame:=TypedBorrowSteps.registeredFrame (atSpan args ⟨601⟩).frame sourceFrame boolId boolTag
  have raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=RootEntryFrame.raw_locals _ _ _
  have dead (slot : Fin 25) (ne1 : slot.val≠1) (ne2 : slot.val≠2) :
      (protectedFrame.locals[slot.val]'(by simpa only [protectedFrame,TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,atSpan] using args.valid slot)).value=.dead := by
    have found : args.frame.locals[slot.val]?=root.frame.locals[slot.val]? := by
      simp only [args,RootArgumentsTwo.result,live,write,cache,atSpan,LocalOperands.cachedLayoutFrame,Array.getElem?_set,
        Ne.symm ne2,ite_false,i2]
      exact other root updated sourceFrame slot.val ne1
    rw [raw] at found
    have row : args.frame.locals[slot.val]?=some (⟨.dead,none⟩ : LocalState Provenance LocalLayout):=found.trans (by simp [slot.isLt])
    exact congrArg LocalState.value (Option.some.inj ((Array.getElem?_eq_getElem (args.valid slot)).symm.trans row))
  have finish:=RootEntryFinish.actual_finish options limits (remaining+1) span frames protectedFrame finalMachine args.body args.size
    (dead ⟨0,by decide⟩ (by decide) (by decide)) (dead ⟨6,by decide⟩ (by decide) (by decide))
    (dead ⟨13,by decide⟩ (by decide) (by decide)) (dead ⟨14,by decide⟩ (by decide) (by decide)) args.noClocks
  have tail:=CurrentCallSourceArguments.tail_of_steps options limits (remaining+1) span frames args sourceMachine place _ _ protection finish
  exact CurrentCallSpatialEntryControl.init_of_steps options limits remaining span initial frames place race debug stackReady input count _ args sourceMachine arguments tail

/-- The common final frame uses the actual optional source ledger. -/
def frame (root : RootFrame) (updated : Immediate Provenance) (sourceFrame : FrameState)
    (count : UInt64) (id : AllocId) (tag : BorTag) :=
  CallEntryFacts.doneRootFrame {TypedBorrowSteps.registeredFrame
    (atSpan (RootArgumentsTwo.result (sourceRoot root updated sourceFrame) count) ⟨601⟩).frame sourceFrame id tag
    with location:=.unwinding ⟨559⟩}

theorem source_some (root : RootFrame) (updated : Immediate Provenance) (borrow : FrameState) (id : AllocId) (tag : BorTag) :
    sourceRoot root updated (borrow.addProtector id tag)=PositiveRootArguments.firstDone root updated borrow id tag := rfl

theorem frame_some (root : RootFrame) (updated : Immediate Provenance) (borrow : FrameState)
    (sourceId : AllocId) (sourceTag : BorTag) (count : UInt64) (id : AllocId) (tag : BorTag) :
    frame root updated (borrow.addProtector sourceId sourceTag) count id tag=
      PositiveRootInstalledFrame.installed root updated count borrow sourceId sourceTag id tag := rfl

/-- Only local storage is compared: this equality adds no fictitious source
protector to the actual optional-ledger frame. -/
theorem locals (root : RootFrame) (updated : Immediate Provenance) (sourceFrame : FrameState)
    (count : UInt64) (id : AllocId) (tag : BorTag) :
    (frame root updated sourceFrame count id tag).locals=
      (PositiveRootInstalledFrame.installed root updated count {} id tag id tag).locals := rfl

theorem metadata (root : RootFrame) (updated : Immediate Provenance) (sourceFrame : FrameState)
    (count : UInt64) (id : AllocId) (tag : BorTag) :
    let f:=frame root updated sourceFrame count id tag
    f.body=root.frame.body ∧f.bodyIdentity=root.frame.bodyIdentity ∧f.functionInstance=root.frame.functionInstance ∧
    f.returnContinuation=root.frame.returnContinuation ∧f.returnPlace=root.frame.returnPlace ∧f.vaList=root.frame.vaList ∧
    f.extra.dataRace=root.frame.extra.dataRace ∧f.extra.borrowTracker=some (sourceFrame.addProtector id tag) ∧f.location=.mir ⟨0,0⟩ := by
  simp only [frame,sourceRoot,CallEntryFacts.doneRootFrame,CallEntryFacts.liveSlot,
    TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,RootArgumentsTwo.result,
    firstLive,firstCache,live,write,cache,atSpan,LocalOperands.cachedLayoutFrame]
  repeat' constructor

/-- Count zero follows the same real root prefix for EVERY updated source
representation and optional source ledger. No source operation is repeated. -/
theorem zero_prefix (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root : RootFrame) (updated : Immediate Provenance) (sourceFrame : FrameState) (id : AllocId) (tag : BorTag)
    (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (machine : Before) (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1) :
    let f:=frame root updated sourceFrame 0 id tag
    ∃result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] f machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine))) ∧
      result.body=RootBody.reflected.body.body ∧result.bodyIdentity=RootBody.reflected.body.identity ∧
      result.functionInstance=RootBody.reflected.functionInstance ∧result.locals.size=25 ∧result.location=.mir ⟨10,0⟩ ∧
      result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      result.returnPlace=f.returnPlace ∧result.extra=f.extra ∧result.returnContinuation=f.returnContinuation ∧
      result.vaList=f.vaList ∧CopyHelperCleanup.AllImmediate result := by
  let f:=frame root updated sourceFrame 0 id tag
  have rows:=locals root updated sourceFrame 0 id tag
  have size : f.locals.size=25:=(congrArg Array.size rows).trans (PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _)
  have cells (index : Fin 25):=PositiveRootInstalledFrame.slot_option root raw updated 0 {} id tag id tag index
  rw [←rows] at cells
  have get (index : Fin 25):=Option.some.inj ((Array.getElem?_eq_getElem (show index.val<f.locals.size by rw [size];exact index.isLt)).symm.trans (cells index))
  have immediate : CopyHelperCleanup.AllImmediate f := by
    change ∀current∈f.locals,∀memory,current.value≠.live (.indirect memory)
    rw [rows]
    exact PositiveRootInstalledFrame.immediate _ raw _ _ _ _ _ _ _
  obtain ⟨body,identity,callee,continuation,returnPlace,varargs,clocks,borrow,location⟩:=metadata root updated sourceFrame 0 id tag
  obtain ⟨current,enabled,mode⟩:=model.defaultTracker
  obtain ⟨result,trace,resultBody,resultIdentity,resultCallee,extra,returnPlace,continuation,varargs,_,resultSize,returnLocation,returnValue,all⟩:=
    RootZeroCompletePrefix.reaches_return options limits remaining span (DuplicatePrefixCallModel.sourceComparator options remaining span machine model)
      model.debugOff fuel fuelEq f machine (body.trans root.body) (identity.trans root.identity) (callee.trans root.callee) location size
      (by simpa using congrArg LocalState.value (get ⟨0,by decide⟩)) (by simpa using congrArg LocalState.layout (get ⟨0,by decide⟩))
      (by simpa using congrArg LocalState.value (get ⟨3,by decide⟩)) (by simpa using congrArg LocalState.value (get ⟨4,by decide⟩))
      (by simpa using congrArg LocalState.value (get ⟨5,by decide⟩)) (by simpa using congrArg LocalState.layout (get ⟨4,by decide⟩))
      (by simpa using congrArg LocalState.layout (get ⟨5,by decide⟩)) (by simpa using congrArg LocalState.value (get ⟨2,by decide⟩))
      (by simpa using congrArg LocalState.layout (get ⟨2,by decide⟩)) (clocks.trans root.noClocks) immediate current enabled mode
      model.ghostOff model.shallow model.unchecked model.noGc model.fixedScheduler
  exact ⟨result,trace,resultBody.trans (body.trans root.body),resultIdentity.trans (identity.trans root.identity),resultCallee.trans (callee.trans root.callee),
    resultSize,returnLocation,returnValue,returnPlace,extra,continuation,varargs,all⟩

/-- Real normalization of the first argument yields equal full initializers,
including either allowed empty-stack thread-cache state. This transports an
existing continuation; no later operation is assumed successful. -/
theorem init_eq_of_arguments (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (before : Before)
    (place : MPlaceTy Provenance) (race : before.dataRace=none) (debug : options.place.debugAssertions=false)
    (ready : CurrentCallPush.StackReadiness before #[]) (left right : Immediate Provenance) (count : UInt64)
    (equal : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate left,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent #[] (CurrentCallSpatialEntryControl.root before #[] place race).frame (CurrentCallPush.preparedMachine before #[]))=
      (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        ⟨.immediate right,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent #[] (CurrentCallSpatialEntryControl.root before #[] place race).frame (CurrentCallPush.preparedMachine before #[]))) :
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) () RootBody.reflected.functionInstance
      RootBody.reflected.body RootCompilerFacts.rootAbi #[.Copy ⟨.immediate left,ActualReferenceMetadata.reference⟩,.Copy (second count)]
      false (.memory place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState)=
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) () RootBody.reflected.functionInstance
      RootBody.reflected.body RootCompilerFacts.rootAbi #[.Copy ⟨.immediate right,ActualReferenceMetadata.reference⟩,.Copy (second count)]
      false (.memory place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState) := by
  let root:=CurrentCallSpatialEntryControl.root before #[] place race
  let machine:=CurrentCallPush.preparedMachine before #[]
  have push:=CurrentCallPush.push options (remaining+1) span limits debug before #[] (.memory place) ready
  have rawEq : CallEntryFacts.rawPushedState #[] before (.memory place)=Storage.withCurrent #[] root.frame machine:=rfl
  have getFrame:=CallEntryLocals.get_frame options limits (remaining+1) span #[] root.frame machine
  have setFrame:=CallEntryLocals.set_frame options limits (remaining+1) span #[] root.frame root.frame machine
  have location : root.frame.location=.unwinding ⟨559⟩:=rfl
  have noCaller : root.frame.trackCallerArg=none:=rfl
  have unchanged : {root.frame with trackCallerArg:=none}=root.frame:=by rw [←noCaller]
  rw [RootCallCore.actual_entry_eq,RootCallCore.actual_entry_eq]
  unfold RootCallCore.core
  simp only [bind,EStateM.bind]
  rw [push,rawEq]
  dsimp only
  rw [getFrame]
  simp only [EStateM.bind,location,pure,EStateM.pure]
  simp only [location] at unchanged
  rw [unchanged,setFrame]
  dsimp only
  rw [equal]
end
end DuplicatePrefix.CurrentCallEmptyProtocolControl
