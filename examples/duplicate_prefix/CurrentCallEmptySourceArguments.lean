import duplicate_prefix.CurrentCallEmptyEntryArguments
import duplicate_prefix.CurrentCallSpatialEntryControl

/-! Actual empty source-copy equations feed the two real ABI arguments under
one FnEntry scope. Effect records only the actual output frame; no Proposed
input or source content family is required by this control consumer. -/
namespace DuplicatePrefix.CurrentCallEmptySourceArguments
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open CurrentCallEmptyTypedEntry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

def doneRoot {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (root : RootFrame) (borrowFrame : FrameState) : RootFrame :=
  let prepared := firstLive root
  let metadata := resultFrame_metadata effect remaining span prepared.frame borrowFrame 1 (prepared.valid i1)
  let shape := CurrentCallEmptyEntryArguments.result_frame_shape effect remaining span prepared.frame borrowFrame 1 (prepared.valid i1)
  {frame := resultFrame effect remaining span prepared.frame borrowFrame 1 (prepared.valid i1)
   size := metadata.2.2.2.2.trans prepared.size
   body := metadata.1.trans prepared.body
   identity := shape.1.trans prepared.identity
   callee := shape.2.1.trans prepared.callee
   noClocks := shape.2.2.trans prepared.noClocks}

/-- The actual lower copy equation is consumed once. Its updated global/tree
survive the enclosing scope; only the original retag mode is restored. -/
theorem arguments (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debug : options.place.debugAssertions=false) (fuel : Nat) (fuelEq : options.limits.validation=fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame)
    (rawLocals : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (before after : Before) (tracker nextTracker : MachineHooks.BorrowState)
    (tracked : before.borrowTracker=some tracker) (afterTracked : after.borrowTracker=some nextTracker)
    (ghost : before.user.payload.ghost=false) (shallow : before.user.payload.validation=.Shallow)
    (afterGhost : after.user.payload.ghost=false) (afterShallow : after.user.payload.validation=.Shallow)
    (argument : DuplicatePrefixSliceArgument.Argument) (effect : Effect options before tracker argument)
    (borrowFrame : FrameState) (count : UInt64)
    (copy : (ExecutionMachine.callHooks (config options (remaining+1) span) limits).copyAllowTransmute ()
      (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0)
      (LocalPlaces.localRuntimePlace frames.size (firstLive root).frame 1 ActualReferenceMetadata.reference).stackView
      (Storage.withCurrent frames (firstLive root).frame (ScopedFrame.entered before tracker .FnEntry))=
      .ok () (Storage.withCurrent frames (doneRoot effect remaining span root borrowFrame).frame after)) :
    let final := RootArgumentsTwo.result (doneRoot effect remaining span root borrowFrame) count
    RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
      (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0) (second count)
      (Storage.withCurrent frames root.frame (ScopedFrame.entered before tracker .FnEntry))=
      .ok (2,2) (Storage.withCurrent frames final.frame after) ∧
    (ExecutionMachine.callHooks (config options (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (config options (remaining+1) span) limits)
        (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0) (second count))
      (Storage.withCurrent frames root.frame before)=
      .ok (2,2) (Storage.withCurrent frames final.frame
        {after with borrowTracker:=some {nextTracker with retagMode:=tracker.retagMode}}) := by
  dsimp only
  have entry1 : (root.frame.locals[1]'(root.valid i1))=(⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    have found : root.frame.locals[1]?=some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by rw [rawLocals];rfl
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i1)).symm.trans found)
  have entry2 : (root.frame.locals[2]'(root.valid i2))=(⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    have found : root.frame.locals[2]?=some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by rw [rawLocals];rfl
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i2)).symm.trans found)
  have other := CurrentCallEmptyEntryArguments.result_other_local effect remaining span (firstLive root).frame borrowFrame
    1 ((firstLive root).valid i1) 2 (by decide)
  have nextSlot : (doneRoot effect remaining span root borrowFrame).frame.locals[2]?=some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    rw [show (doneRoot effect remaining span root borrowFrame).frame.locals[2]?=(firstLive root).frame.locals[2]? from other]
    simpa only [firstLive,RootFrameData.live,RootFrameData.write,firstCache,RootFrameData.cache,
      RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,Array.getElem?_set,i1,i2,
      show (2 : Nat)≠1 by decide,show (1 : Nat)≠2 by decide,ite_false]
      using (Array.getElem?_eq_getElem (root.valid i2)).trans (congrArg some entry2)
  have nextEntry := Option.some.inj ((Array.getElem?_eq_getElem ((doneRoot effect remaining span root borrowFrame).valid i2)).symm.trans nextSlot)
  have body := RootArgumentsTwo.body options limits remaining span debug fuel fuelEq frames root
    (doneRoot effect remaining span root borrowFrame) (ScopedFrame.entered before tracker .FnEntry) after
    (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base argument 0 ActualReferenceMetadata.reference).imm count
    (congrArg LocalState.value entry1) (congrArg LocalState.layout entry1)
    (congrArg LocalState.value nextEntry) (congrArg LocalState.layout nextEntry) ghost shallow afterGhost afterShallow copy
  exact ⟨body,ScopedFrame.changed_state _ (Storage.withCurrent frames root.frame before)
    (Storage.withCurrent frames (RootArgumentsTwo.result (doneRoot effect remaining span root borrowFrame) count).frame after)
    tracker nextTracker .FnEntry (2,2) tracked afterTracked body⟩

@[simp] theorem result_returnPlace {options before tracker argument}
    (effect : Effect options before tracker argument) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root : RootFrame) (borrowFrame : FrameState) (count : UInt64) :
    (RootArgumentsTwo.result (doneRoot effect remaining span root borrowFrame) count).frame.returnPlace=root.frame.returnPlace := by
  exact (resultFrame_metadata effect remaining span (firstLive root).frame borrowFrame 1 ((firstLive root).valid i1)).2.2.1

end
end DuplicatePrefix.CurrentCallEmptySourceArguments
