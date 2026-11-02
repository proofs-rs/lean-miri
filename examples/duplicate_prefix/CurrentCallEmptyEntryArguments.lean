import duplicate_prefix.CurrentCallEmptyTypedEntry
import duplicate_prefix.CurrentCallArguments

/-! Actual paired empty arguments under one FnEntry scope. Exact source effects
are retained for the subsequent Bool-only entry consumer. -/
namespace DuplicatePrefix.CurrentCallEmptyEntryArguments
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter Miri.TreeBorrows
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open CurrentCallEmptyTypedEntry TypedBorrowSteps ReferenceBorrowDriver
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def nextTracker {options before tracker argument} (effect : Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) : MachineHooks.BorrowState :=
  match effect.allocation with
  | none => {tracker with global := {tracker.global with nextPointerTag := TypedRetagEmpty.successorTag tracker.global.nextPointerTag fresh},retagMode := .FnEntry}
  | some _ => registeredTracker (allocatedTracker {tracker with retagMode := .FnEntry} fresh) tracker.global.nextPointerTag

theorem result_tracked {options before tracker argument} (effect : Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size) :
    (resultMachine effect fresh remaining span frames frame borrowFrame localId valid).borrowTracker = some (nextTracker effect fresh) := by
  cases effect <;> rfl

theorem result_settings {options before tracker argument} (effect : Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (ghost : before.user.payload.ghost = false) :
    (resultMachine effect fresh remaining span frames frame borrowFrame localId valid).user.payload.ghost = false ∧
    (resultMachine effect fresh remaining span frames frame borrowFrame localId valid).user.payload.validation = before.user.payload.validation := by
  cases effect <;> exact ⟨by first | exact ghost | rfl,rfl⟩

theorem result_frame_shape {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size) :
    (resultFrame effect remaining span frame borrowFrame localId valid).bodyIdentity = frame.bodyIdentity ∧
    (resultFrame effect remaining span frame borrowFrame localId valid).functionInstance = frame.functionInstance ∧
    (resultFrame effect remaining span frame borrowFrame localId valid).extra.dataRace = frame.extra.dataRace := by
  cases effect <;> exact ⟨rfl,rfl,rfl⟩

theorem result_other_local {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frame : CompilerFrameContext.ActualFrame)
    (borrowFrame : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size) (other : MIR.LocalId)
    (different : other ≠ localId) :
    (resultFrame effect remaining span frame borrowFrame localId valid).locals[other]? = frame.locals[other]? := by
  cases effect <;> simp only [resultFrame,Effect.allocation,registered,copied,CurrentCallEmptyReferenceValidation.writtenFrame,
    registeredFrame,TypedRetagEntry.frameWithBorrow,Array.getElem?_set,Ne.symm different,ite_false]

/-- Actual empty argument setup, universally in count. No source allocation,
loan or origin appears outside the exact finite Effect output. -/
theorem arguments
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (identity : LocalsIdentity) (count : UInt64) :
    let root := RootFrameData.raw before (CurrentCallArguments.destination place) identity input.machine.settings.noDataRace
    let prepared := firstLive root
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    ∃ effect : Effect options before tracker argument,
    ∃ firstDone : RootFrame,
      firstDone.frame = resultFrame effect remaining span prepared.frame {} 1 (prepared.valid i1) ∧
      (RootArgumentsTwo.result firstDone count).frame.returnPlace = CurrentCallArguments.destination place ∧
      (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
        (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
          (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0) (second count))
        (Storage.withCurrent frames root.frame before) =
        .ok (2,2) (Storage.withCurrent frames (RootArgumentsTwo.result firstDone count).frame
          {(resultMachine effect fresh remaining span frames prepared.frame {} 1 (prepared.valid i1)) with
            borrowTracker := some {(nextTracker effect fresh) with retagMode := tracker.retagMode}}) := by
  dsimp only
  let root := RootFrameData.raw before (CurrentCallArguments.destination place) identity input.machine.settings.noDataRace
  let prepared := firstLive root
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  have rawLocals : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) :=
    RootEntryFrame.raw_locals before (CurrentCallArguments.destination place) identity
  have entry1 : (root.frame.locals[1]'(root.valid i1)) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    have found : root.frame.locals[1]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by rw [rawLocals];rfl
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i1)).symm.trans found)
  have entry2 : (root.frame.locals[2]'(root.valid i2)) = (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    have found : root.frame.locals[2]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by rw [rawLocals];rfl
    exact Option.some.inj ((Array.getElem?_eq_getElem (root.valid i2)).symm.trans found)
  have borrow : prepared.frame.extra.borrowTracker = some {} :=
    RootEntryFrame.raw_borrow before (CurrentCallArguments.destination place) identity tracker input.machine.state.enabled
  have live : (prepared.frame.locals[1]'(prepared.valid i1)).value = .live (.immediate .uninit) := by
    simp only [prepared,firstLive,RootFrameData.live,RootFrameData.write,Array.getElem_set_self,i1]
  have cached : (prepared.frame.locals[1]'(prepared.valid i1)).layout = some ActualReferenceMetadata.reference := by
    simp only [prepared,firstLive,RootFrameData.live,RootFrameData.write,firstCache,RootFrameData.cache,
      LocalOperands.cachedLayoutFrame,Array.getElem_set_self,i1]
  obtain ⟨effect,copy⟩ := CurrentCallEmptyTypedEntry.copy_argument options limits remaining span before tracker argument place call data input
    frames prepared.frame {} borrow 1 (prepared.valid i1) .uninit live cached prepared.noClocks
  have shape := result_frame_shape effect remaining span prepared.frame {} 1 (prepared.valid i1)
  have metadata := resultFrame_metadata effect remaining span prepared.frame {} 1 (prepared.valid i1)
  let firstDone : RootFrame := {
    frame := resultFrame effect remaining span prepared.frame {} 1 (prepared.valid i1)
    size := metadata.2.2.2.2.trans prepared.size
    body := metadata.1.trans prepared.body
    identity := shape.1.trans prepared.identity
    callee := shape.2.1.trans prepared.callee
    noClocks := shape.2.2.trans prepared.noClocks }
  have other := result_other_local effect remaining span prepared.frame {} 1 (prepared.valid i1) 2 (by decide)
  have nextSlot : firstDone.frame.locals[2]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
    rw [show firstDone.frame.locals[2]? = prepared.frame.locals[2]? from other]
    simpa only [prepared,firstLive,RootFrameData.live,RootFrameData.write,firstCache,RootFrameData.cache,
      RootFrameData.atSpan,LocalOperands.cachedLayoutFrame,Array.getElem?_set,i1,i2,show (2 : Nat) ≠ 1 by decide,show (1 : Nat) ≠ 2 by decide,ite_false]
      using (Array.getElem?_eq_getElem (root.valid i2)).trans (congrArg some entry2)
  have nextEntry := Option.some.inj ((Array.getElem?_eq_getElem (firstDone.valid i2)).symm.trans nextSlot)
  have settings := result_settings effect fresh remaining span frames prepared.frame {} 1 (prepared.valid i1) input.machine.settings.ghostOff
  have fuelPositive : 0 < options.limits.validation := by
    have budget := input.machine.resources.configuredFuel.2.2.2
    unfold DuplicatePrefixCallSpecification.work at budget;omega
  let fuel := options.limits.validation-1
  have fuelEq : options.limits.validation = fuel+1 := by dsimp only [fuel];omega
  have body := RootArgumentsTwo.body options limits remaining span input.machine.settings.debugOff fuel fuelEq frames root firstDone
    (ScopedFrame.entered before tracker .FnEntry)
    (resultMachine effect fresh remaining span frames prepared.frame {} 1 (prepared.valid i1))
    (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base argument 0 ActualReferenceMetadata.reference).imm count
    (congrArg LocalState.value entry1) (congrArg LocalState.layout entry1)
    (congrArg LocalState.value nextEntry) (congrArg LocalState.layout nextEntry)
    input.machine.settings.ghostOff input.machine.settings.shallow settings.1 (settings.2.trans input.machine.settings.shallow) copy
  refine ⟨effect,firstDone,rfl,?_,?_⟩
  · exact metadata.2.2.1.trans (RootEntryFrame.raw_control before (CurrentCallArguments.destination place) identity).2.2.2.1
  · exact ScopedFrame.changed_state _ (Storage.withCurrent frames root.frame before)
      (Storage.withCurrent frames (RootArgumentsTwo.result firstDone count).frame
        (resultMachine effect fresh remaining span frames prepared.frame {} 1 (prepared.valid i1))) tracker
      (nextTracker effect fresh) .FnEntry (2,2) input.machine.state.enabled
      (result_tracked effect fresh remaining span frames prepared.frame {} 1 (prepared.valid i1)) body

end
end DuplicatePrefix.CurrentCallEmptyEntryArguments

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallEmptyEntryArguments." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "empty argument pair depends on unapproved axiom {dependency}"
