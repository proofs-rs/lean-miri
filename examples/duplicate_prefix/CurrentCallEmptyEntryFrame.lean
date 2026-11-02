import duplicate_prefix.CurrentCallEmptyEntry
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.RootZeroCompletePrefix

/-! Structural facts for the actual empty-entry frame. These facts concern
locals and control; the exact finite effect retains its own protector list. -/
namespace DuplicatePrefix.CurrentCallEmptyEntryFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
open CurrentCallEmptyTypedEntry
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def adjusted {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) : Immediate Provenance :=
  (DuplicatePrefixSliceArgument.rawValue (ActualReferenceContext.config options remaining span).access.runtime.base
    effect.output 0 ActualReferenceMetadata.reference).imm

/-- The finite copy effect changes local 1 to its actual output immediate.
Only locals are compared here; branch-specific protector extras are retained. -/
theorem copied_locals {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (root : RootFrame) :
    (resultFrame effect remaining span (firstLive root).frame {} 1 ((firstLive root).valid i1)).locals =
      (write (firstLive root) i1 (adjusted effect remaining span)).frame.locals := by
  cases effect <;>
    simp [resultFrame,copied,registered,Effect.allocation,Effect.output,adjusted,
      CurrentCallEmptyReferenceValidation.writtenFrame,registeredFrame,TypedRetagEntry.frameWithBorrow,
      RootFrameData.write,i1,Array.set_set]

/-- The installed local array has the standard two-argument shape, independently
of whether the empty source registered a real protector. -/
theorem installed_locals {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (root firstDone : RootFrame)
    (copied : firstDone.frame = resultFrame effect remaining span (firstLive root).frame {} 1 ((firstLive root).valid i1))
    (count : UInt64) (borrow : FrameState) (id : AllocId) (tag : BorTag) :
    (CallEntryFacts.doneRootFrame {registeredFrame (atSpan (RootArgumentsTwo.result firstDone count) ⟨601⟩).frame
      borrow id tag with location := .unwinding ⟨559⟩}).locals =
    (PositiveRootInstalledFrame.installed root (adjusted effect remaining span) count {} id tag id tag).locals := by
  have locals := copied_locals effect remaining span root
  rw [←copied] at locals
  simp only [CallEntryFacts.doneRootFrame,CallEntryFacts.liveSlot,registeredFrame,TypedRetagEntry.frameWithBorrow,
    RootArgumentsTwo.result,PositiveRootInstalledFrame.installed,PositiveRootArguments.firstDone,
    PositiveRootArguments.protectedRoot,RootFrameData.atSpan,RootFrameData.write,RootFrameData.live,
    RootFrameData.cache,LocalOperands.cachedLayoutFrame]
  simp only [Array.getElem_set_self,Array.set_set]
  congr 4
  congr 1

/-- The exact installed empty-entry frame; its borrow extras remain explicit. -/
def installed (firstDone : RootFrame) (count : UInt64) (borrow : FrameState) (id : AllocId) (tag : BorTag) :=
  CallEntryFacts.doneRootFrame {registeredFrame (atSpan (RootArgumentsTwo.result firstDone count) ⟨601⟩).frame
    borrow id tag with location := .unwinding ⟨559⟩}

theorem installed_slot {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (root firstDone : RootFrame)
    (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (copied : firstDone.frame = resultFrame effect remaining span (firstLive root).frame {} 1 ((firstLive root).valid i1))
    (count : UInt64) (borrow : FrameState) (id : AllocId) (tag : BorTag) (i : Fin 25) :
    (installed firstDone count borrow id tag).locals[i.val]? = some (
    if 14 = i.val ∨ 13 = i.val ∨ 6 = i.val ∨ 0 = i.val then ⟨.live (.immediate .uninit),none⟩
    else if 2 = i.val then ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 count)))),some RootCompilerFacts.usizeLayout⟩
    else if 1 = i.val then ⟨.live (.immediate (adjusted effect remaining span)),some ActualReferenceMetadata.reference⟩
    else ⟨.dead,none⟩) := by
  rw [show (installed firstDone count borrow id tag).locals = _ from installed_locals effect remaining span root firstDone copied count borrow id tag]
  exact PositiveRootInstalledFrame.slot_option root raw (adjusted effect remaining span) count {} id tag id tag i

theorem installed_immediate {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (root firstDone : RootFrame)
    (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (copied : firstDone.frame = resultFrame effect remaining span (firstLive root).frame {} 1 ((firstLive root).valid i1))
    (count : UInt64) (borrow : FrameState) (id : AllocId) (tag : BorTag) :
    CopyHelperCleanup.AllImmediate (installed firstDone count borrow id tag) := by
  intro current member memory
  rw [show (installed firstDone count borrow id tag).locals = _ from installed_locals effect remaining span root firstDone copied count borrow id tag] at member
  exact PositiveRootInstalledFrame.immediate root raw (adjusted effect remaining span) count {} id tag id tag current member memory

theorem installed_control (firstDone : RootFrame) (count : UInt64) (borrow : FrameState) (id : AllocId) (tag : BorTag) :
    (installed firstDone count borrow id tag).body = RootBody.reflected.body.body ∧
    (installed firstDone count borrow id tag).bodyIdentity = RootBody.reflected.body.identity ∧
    (installed firstDone count borrow id tag).functionInstance = RootBody.reflected.functionInstance ∧
    (installed firstDone count borrow id tag).location = .mir ⟨0,0⟩ ∧
    (installed firstDone count borrow id tag).locals.size = 25 ∧
    (installed firstDone count borrow id tag).extra.dataRace = none := by
  simp only [installed,CallEntryFacts.doneRootFrame,CallEntryFacts.liveSlot,registeredFrame,TypedRetagEntry.frameWithBorrow,
    RootArgumentsTwo.result,RootFrameData.atSpan,RootFrameData.write,RootFrameData.live,RootFrameData.cache,
    LocalOperands.cachedLayoutFrame,Array.size_modify,Array.size_set]
  exact ⟨firstDone.body,firstDone.identity,firstDone.callee,rfl,firstDone.size,firstDone.noClocks⟩

/-- Raw configuration scope survives the actual empty-copy effect. -/
theorem model_after_arguments {options before tracker argument} (effect : Effect options before tracker argument)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrow : FrameState) (localId : MIR.LocalId) (valid : localId < frame.locals.size)
    (model : DuplicatePrefixCallModel.Model options remaining span before)
    (enabled : before.borrowTracker = some tracker) :
    DuplicatePrefixCallModel.Model options remaining span
      (CurrentCallEmptyEntryBool.afterArgumentsMachine effect fresh remaining span frames frame borrow localId valid) := by
  have settings := CurrentCallEmptyEntryArguments.result_settings effect fresh remaining span frames frame borrow localId valid model.ghostOff
  obtain ⟨old,oldEnabled,oldMode⟩ := model.defaultTracker
  have same : old = tracker := Option.some.inj (oldEnabled.symm.trans enabled)
  have mode : tracker.retagMode = .Default := same ▸ oldMode
  refine ⟨model.debugOff,model.preciseOff,model.implicitOff,settings.1,settings.2.trans model.shallow,
    ⟨CurrentCallEmptyEntryBool.afterArgumentsTracker effect fresh,rfl,?_⟩,?_,?_,?_,?_,?_,?_,model.nullComparator,model.sourceMatches⟩
  · exact mode
  · cases effect <;> exact model.noDataRace
  · cases effect <;> exact model.noBackend
  · cases effect <;> exact model.metadata
  · cases effect <;> exact model.fixedScheduler
  · have eq : (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
          (CurrentCallEmptyEntryBool.afterArgumentsMachine effect fresh remaining span frames frame borrow localId valid).user =
        (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user := by
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      cases effect <;> rfl
    rw [eq];exact model.unchecked
  · have eq : (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl
          (CurrentCallEmptyEntryBool.afterArgumentsMachine effect fresh remaining span frames frame borrow localId valid).user =
        (PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl before.user := by
      rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
      cases effect <;> rfl
    rw [eq];exact model.noGc

/-- Bool protection and the actual allocation replacement preserve the raw
configuration scope. The real read/write tree remains in the output machine. -/
theorem model_after_protection (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (frames : Array CompilerFrameContext.ActualFrame)
    (frame : CompilerFrameContext.ActualFrame) (borrow : FrameState)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (tracker : MachineHooks.BorrowState)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (enabled : machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind) (tree : BorrowTree)
    (updated : Allocation Provenance BorrowTree) :
    let retagged := ReturnProtection.borrowedState frames frame borrow machine tracker fresh id entry tree
    DuplicatePrefixCallModel.Model options remaining span
      {retagged.machine with memory := {retagged.machine.memory with live :=
        (retagged.machine.memory.live.filter fun row => row.1 != id).push (id,{entry with allocation := updated})}} := by
  obtain ⟨old,oldEnabled,oldMode⟩ := model.defaultTracker
  have same : old = tracker := Option.some.inj (oldEnabled.symm.trans enabled)
  have mode : tracker.retagMode = .Default := same ▸ oldMode
  exact ⟨model.debugOff,model.preciseOff,model.implicitOff,model.ghostOff,model.shallow,
    ⟨registeredTracker (allocatedTracker tracker fresh) tracker.global.nextPointerTag,rfl,mode⟩,
    model.noDataRace,model.noBackend,model.metadata,model.fixedScheduler,model.unchecked,model.noGc,
    model.nullComparator,model.sourceMatches⟩

/-- The actual count-zero body prefix for the installed finite-effect frame.
The endpoint derives `model` and `fuelEq` from its original proposed input. -/
theorem zero_reaches_return {options before tracker argument} (effect : Effect options before tracker argument)
    (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (root firstDone : RootFrame)
    (raw : root.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (copied : firstDone.frame = resultFrame effect remaining span (firstLive root).frame {} 1 ((firstLive root).valid i1))
    (borrow : FrameState) (id : AllocId) (tag : BorTag) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (fuel : Nat) (fuelEq : options.limits.validation = fuel+1) :
    let frame := installed firstDone 0 borrow id tag
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (ActualReferenceContext.config options (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span
          (RootZeroCompleteState.tick options remaining span machine))) ∧
      result.body = RootBody.reflected.body.body ∧ result.bodyIdentity = RootBody.reflected.body.identity ∧
      result.functionInstance = RootBody.reflected.functionInstance ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      result.returnPlace = frame.returnPlace ∧ result.extra = frame.extra ∧
      result.returnContinuation = frame.returnContinuation ∧ result.vaList = frame.vaList ∧
      CopyHelperCleanup.AllImmediate result := by
  let frame := installed firstDone 0 borrow id tag
  obtain ⟨body,identity,callee,location,size,clocks⟩ := installed_control firstDone 0 borrow id tag
  have cells (i : Fin 25) := installed_slot effect remaining span root firstDone raw copied 0 borrow id tag i
  have slots (i : Fin 25) := Option.some.inj ((Array.getElem?_eq_getElem (by rw [size];exact i.isLt)).symm.trans (cells i))
  have immediate := installed_immediate effect remaining span root firstDone raw copied 0 borrow id tag
  obtain ⟨current,enabled,mode⟩ := model.defaultTracker
  obtain ⟨result,trace,resultBody,resultIdentity,resultCallee,extra,returnPlace,continuation,varargs,_,resultSize,returnLocation,returnValue,all⟩ :=
    RootZeroCompletePrefix.reaches_return options limits remaining span
      (DuplicatePrefixCallModel.sourceComparator options remaining span machine model)
      model.debugOff fuel fuelEq frame machine body identity callee location size
      (by simpa using congrArg LocalState.value (slots ⟨0,by decide⟩))
      (by simpa using congrArg LocalState.layout (slots ⟨0,by decide⟩))
      (by simpa using congrArg LocalState.value (slots ⟨3,by decide⟩))
      (by simpa using congrArg LocalState.value (slots ⟨4,by decide⟩))
      (by simpa using congrArg LocalState.value (slots ⟨5,by decide⟩))
      (by simpa using congrArg LocalState.layout (slots ⟨4,by decide⟩))
      (by simpa using congrArg LocalState.layout (slots ⟨5,by decide⟩))
      (by simpa using congrArg LocalState.value (slots ⟨2,by decide⟩))
      (by simpa using congrArg LocalState.layout (slots ⟨2,by decide⟩))
      clocks immediate current enabled mode model.ghostOff model.shallow model.unchecked model.noGc model.fixedScheduler
  exact ⟨result,trace,resultBody.trans body,resultIdentity.trans identity,resultCallee.trans callee,resultSize,
    returnLocation,returnValue,returnPlace,extra,continuation,varargs,all⟩

end
end DuplicatePrefix.CurrentCallEmptyEntryFrame

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallEmptyEntryFrame." then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty frame/body dependency {dependency}"
