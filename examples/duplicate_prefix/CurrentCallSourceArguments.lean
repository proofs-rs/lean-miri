import duplicate_prefix.CurrentCallTypedSourceCopy
import duplicate_prefix.RootArgumentsTwo
import duplicate_prefix.RootEntryTail

namespace DuplicatePrefix.CurrentCallSourceArguments
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def doneRoot (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root : RootFrame) (borrowFrame : FrameState) (pointer : Pointer Provenance) (len : UInt64)
    (id : AllocId) (tag : BorTag) : RootFrame :=
  let prepared := firstLive root
  let copied := CurrentCallTypedSourceCopy.copiedFrame options remaining span prepared.frame 1 (prepared.valid i1) pointer len
  { frame := CurrentCallTypedSourceCopy.writtenFrame options remaining span copied borrowFrame 1
      (by simpa only [copied,CurrentCallTypedSourceCopy.copiedFrame,Array.size_set,i1] using prepared.valid i1) pointer len id tag
    size := by simpa only [CurrentCallTypedSourceCopy.writtenFrame,copied,CurrentCallTypedSourceCopy.copiedFrame,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,Array.size_set] using prepared.size
    body := prepared.body
    identity := prepared.identity
    callee := prepared.callee
    noClocks := prepared.noClocks }

/-- The source producer's actual copy equation is consumed once. The second
argument and the enclosing mode scope are the existing real call operations. -/
theorem arguments (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions = false) (fuel : Nat)
    (fuelEq : options.limits.validation = fuel + 1)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (rawLocals : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (before after : Before) (tracker nextTracker : MachineHooks.BorrowState)
    (tracked : before.borrowTracker = some tracker) (afterTracked : after.borrowTracker = some nextTracker)
    (ghost : before.user.payload.ghost = false) (shallow : before.user.payload.validation = .Shallow)
    (afterGhost : after.user.payload.ghost = false) (afterShallow : after.user.payload.validation = .Shallow)
    (borrowFrame : FrameState) (pointer : Pointer Provenance) (len count : UInt64) (id : AllocId) (tag : BorTag)
    (copy : (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).copyAllowTransmute ()
      ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩
      (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames (firstLive root).frame (ScopedFrame.entered before tracker .FnEntry)) =
      .ok () (Storage.withCurrent frames (doneRoot options remaining span root borrowFrame pointer len id tag).frame after)) :
    let done := doneRoot options remaining span root borrowFrame pointer len id tag
    let final := RootArgumentsTwo.result done count
    RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
      ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩
      (second count) (Storage.withCurrent frames root.frame (ScopedFrame.entered before tracker .FnEntry)) =
      .ok (2,2) (Storage.withCurrent frames final.frame after) ∧
    (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
        ⟨.immediate (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm,ActualReferenceMetadata.reference⟩ (second count))
      (Storage.withCurrent frames root.frame before) =
      .ok (2,2) (Storage.withCurrent frames final.frame
        {after with borrowTracker := some {nextTracker with retagMode := tracker.retagMode}}) := by
  dsimp only
  have entry1 : (root.frame.locals[1]'(root.valid i1)) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    have found : root.frame.locals[1]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by rw [rawLocals];rfl
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i1)).symm.trans found)
  have dead2 : (root.frame.locals[2]'(root.valid i2)).value = .dead := by
    simp [rawLocals]
  have cache2 : (root.frame.locals[2]'(root.valid i2)).layout = none := by
    simp [rawLocals]
  have nextDead : ((doneRoot options remaining span root borrowFrame pointer len id tag).frame.locals[2]'((doneRoot options remaining span root borrowFrame pointer len id tag).valid i2)).value = .dead := by
    simpa [doneRoot,CurrentCallTypedSourceCopy.writtenFrame,CurrentCallTypedSourceCopy.copiedFrame,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,firstLive,RootFrameData.live,
      RootFrameData.write,firstCache,RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,Array.getElem_set,i1,i2] using dead2
  have nextCache : ((doneRoot options remaining span root borrowFrame pointer len id tag).frame.locals[2]'((doneRoot options remaining span root borrowFrame pointer len id tag).valid i2)).layout = none := by
    simpa [doneRoot,CurrentCallTypedSourceCopy.writtenFrame,CurrentCallTypedSourceCopy.copiedFrame,
      TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,firstLive,RootFrameData.live,
      RootFrameData.write,firstCache,RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,Array.getElem_set,i1,i2] using cache2
  have body := RootArgumentsTwo.body options limits remaining span debug fuel fuelEq frames root
    (doneRoot options remaining span root borrowFrame pointer len id tag)
    (ScopedFrame.entered before tracker .FnEntry) after
    (CurrentCallTypedSourceCopy.value options remaining span pointer len).imm count
    (congrArg LocalState.value entry1) (congrArg LocalState.layout entry1) nextDead nextCache
    ghost shallow afterGhost afterShallow copy
  exact ⟨body,ScopedFrame.changed_state _ (Storage.withCurrent frames root.frame before)
    (Storage.withCurrent frames (RootArgumentsTwo.result (doneRoot options remaining span root borrowFrame pointer len id tag) count).frame after)
    tracker nextTracker .FnEntry (2,2) tracked afterTracked body⟩

@[simp] theorem result_returnPlace (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root : RootFrame) (borrowFrame : FrameState) (pointer : Pointer Provenance) (len count : UInt64) (id : AllocId) (tag : BorTag) :
    (RootArgumentsTwo.result (doneRoot options remaining span root borrowFrame pointer len id tag) count).frame.returnPlace = root.frame.returnPlace := by
  simp only [RootArgumentsTwo.result,doneRoot,CurrentCallTypedSourceCopy.writtenFrame,
    TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,CurrentCallTypedSourceCopy.copiedFrame,
    RootFrameData.write,RootFrameData.live,RootFrameData.cache,RootFrameData.atSpan,
    firstLive,firstCache,LocalOperands.cachedLayoutFrame]


@[simp] theorem result_borrowFrame (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root : RootFrame) (borrowFrame : FrameState) (pointer : Pointer Provenance) (len count : UInt64) (id : AllocId) (tag : BorTag) :
    (RootArgumentsTwo.result (doneRoot options remaining span root borrowFrame pointer len id tag) count).frame.extra.borrowTracker =
      some (borrowFrame.addProtector id tag) := by
  simp only [RootArgumentsTwo.result,doneRoot,CurrentCallTypedSourceCopy.writtenFrame,
    TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,CurrentCallTypedSourceCopy.copiedFrame,
    RootFrameData.write,RootFrameData.live,RootFrameData.cache,RootFrameData.atSpan,
    firstLive,firstCache,LocalOperands.cachedLayoutFrame]

theorem result_other_local (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root : RootFrame) (borrowFrame : FrameState) (pointer : Pointer Provenance) (len count : UInt64) (id : AllocId) (tag : BorTag)
    (slot : Nat) (ne1 : slot ≠ 1) (ne2 : slot ≠ 2) :
    (RootArgumentsTwo.result (doneRoot options remaining span root borrowFrame pointer len id tag) count).frame.locals[slot]? =
      root.frame.locals[slot]? := by
  simp only [RootArgumentsTwo.result,doneRoot,CurrentCallTypedSourceCopy.writtenFrame,CurrentCallTypedSourceCopy.copiedFrame,
    TypedBorrowSteps.registeredFrame,TypedRetagEntry.frameWithBorrow,firstLive,firstCache,
    RootFrameData.write,RootFrameData.live,RootFrameData.cache,RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,
    Array.getElem?_set,Ne.symm ne1,Ne.symm ne2,ite_false,i1,i2]

private theorem return_abi (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (state : RootState) :
    (ExecutionMachine.callHooks (config options remaining span) limits).checkArgumentCompat ()
      RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret state = .ok true state := by
  change (config options remaining span).calls.compiler.checkArgumentCompat () _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
  exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _

/-- The suffix has the exact local-zero span and return ABI query before
protection, then the source preamble/count/afterFrameInit/pushDone sequence. -/
theorem tail_of_steps (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame) (machine : Before)
    (place : MPlaceTy Provenance) (after protectedState : RootState)
    (protect : (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan root ⟨601⟩).frame machine) = .ok () protectedState)
    (finish : RootEntryFinish.finish (ExecutionMachine.callHooks (config options remaining span) limits)
      protectedState = .ok () after) :
    RootEntryTail.tail (ExecutionMachine.callHooks (config options remaining span) limits) place
      (Storage.withCurrent frames root.frame machine) = .ok () after := by
  have localSpan := CallEntryLocals.root_span0 options limits remaining span frames root.frame machine root.body root.identity root.callee
  have getFrame := CallEntryLocals.get_frame options limits remaining span frames root.frame machine
  have setFrame := CallEntryLocals.set_frame options limits remaining span frames root.frame (atSpan root ⟨601⟩).frame machine
  have compat := return_abi options limits remaining span (Storage.withCurrent frames (atSpan root ⟨601⟩).frame machine)
  unfold RootEntryTail.tail RootCallCore.spanAt
  simp only [bind,EStateM.bind]
  rw [localSpan]
  dsimp only
  rw [getFrame]
  dsimp only
  dsimp only [atSpan] at setFrame
  rw [setFrame]
  dsimp only
  dsimp only [atSpan] at compat
  rw [compat]
  simp only [EStateM.bind,ite_true]
  dsimp only [atSpan] at protect
  rw [protect]
  exact finish


end
end DuplicatePrefix.CurrentCallSourceArguments
open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if (name.toString.splitOn "DuplicatePrefix.CurrentCallSourceArguments.").length != 1 then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved source arguments dependency {dependency}"
