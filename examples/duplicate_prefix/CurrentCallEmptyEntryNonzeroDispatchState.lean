import duplicate_prefix.CurrentCallEmptyEntryRoot
import duplicate_prefix.CurrentCallEmptyEntryFrame
import duplicate_prefix.PushThread
namespace DuplicatePrefix.CurrentCallEmptyEntryNonzeroDispatchState
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.Interpreter
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open CurrentCallEmptyTypedEntry CurrentCallEmptyEntryBool CurrentCallEmptyEntryFrame
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency true
set_option backward.dsimp.instances false

variable {options limits remaining span before tracker argument place call data}
    {input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data}

def root (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data) : RootFrame :=
  CurrentCallEntry.root before #[] place input.machine.settings.noDataRace

theorem fresh (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data) :
    tracker.global.nextPointerTag.value<18446744073709551615 :=
  CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources

def sourceTracker (out : CurrentCallEmptyEntryRoot.Output input #[]) : MachineHooks.BorrowState :=
  afterArgumentsTracker out.effect (fresh input)

def sourceMachine (out : CurrentCallEmptyEntryRoot.Output input #[]) : Before :=
  afterArgumentsMachine out.effect (fresh input) remaining span #[] (firstLive (root input)).frame {} 1 ((firstLive (root input)).valid i1)

def frame (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) : CompilerFrameContext.ActualFrame :=
  installed out.firstDone count (CurrentCallEmptyEntryRoot.sourceBorrow out.effect {}) out.physical.id (sourceTracker out).global.nextPointerTag

def machine (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) : Before :=
  let changed := atSpan (RootArgumentsTwo.result out.firstDone count) ⟨601⟩
  let retagged := ReturnProtection.borrowedState #[] changed.frame (CurrentCallEmptyEntryRoot.sourceBorrow out.effect {})
    (sourceMachine out) (sourceTracker out) out.room out.physical.id out.physical.entry out.certificate.output.child.tree
  {retagged.machine with memory := {retagged.machine.memory with live :=
    ((retagged.machine.memory.live.filter fun row => row.1 != out.physical.id).push (out.physical.id,{out.physical.entry with allocation:=out.updated}))}}

def held (out : CurrentCallEmptyEntryRoot.Output input #[]) : MachineHooks.BorrowState :=
  ⟨out.certificate.output.global,tracker.retagMode⟩

theorem held_global (out : CurrentCallEmptyEntryRoot.Output input #[]) :
    (held out).global=(GeneralBorrowFnEntryRegistration.registered (sourceTracker out).global
      (CurrentCallEmptyEntryBool.rootSource out.effect) out.physical.id out.room).1 := out.certificate.globalEq

theorem tracked (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) :
    (machine out count).borrowTracker=some (held out) := by
  change some ({global:=(GeneralBorrowFnEntryRegistration.registered (sourceTracker out).global
    (CurrentCallEmptyEntryBool.rootSource out.effect) out.physical.id out.room).1,retagMode:=tracker.retagMode} : MachineHooks.BorrowState)=
    some ({global:=out.certificate.output.global,retagMode:=tracker.retagMode} : MachineHooks.BorrowState)
  rw [out.certificate.globalEq]
  rfl

theorem copied (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) :
    out.firstDone.frame=resultFrame out.effect remaining span (firstLive (root input)).frame {} 1 ((firstLive (root input)).valid i1) := facts.1

theorem actual (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) :
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0),.Copy (second count)]
      false (CurrentCallArguments.destination place) (.stop true) (⟨⟨#[]⟩,before⟩ : RootState)=
      .ok () (Storage.withCurrent #[] (frame out count) (machine out count)) := facts.2.1

theorem destination (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) : (frame out count).returnPlace=CurrentCallArguments.destination place := facts.2.2.1

theorem model (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) :
    DuplicatePrefixCallModel.Model options remaining span (machine out count) := by
  let transported := CurrentCallPush.prepared_input input #[]
  have initial := model_after_arguments out.effect (fresh input) remaining span #[] (firstLive (root input)).frame {} 1
    ((firstLive (root input)).valid i1) transported.machine.settings transported.machine.state.enabled
  exact model_after_protection options remaining span #[] (atSpan (RootArgumentsTwo.result out.firstDone count) ⟨601⟩).frame
    (CurrentCallEmptyEntryRoot.sourceBorrow out.effect {}) (sourceMachine out) (sourceTracker out) initial rfl
    out.room out.physical.id out.physical.entry out.certificate.output.child.tree out.updated

theorem origins (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (facts : CurrentCallEmptyEntryRoot.Facts out count) :
    DuplicatePrefixTypeCacheOrigins.Origins (machine out count).user.payload.payload.user.types := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,origins,_,_,_,_⟩ := facts
  exact origins

theorem addresses (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) :
    (machine out count).user.addresses=before.user.addresses := by
  change (sourceMachine out).user.addresses=before.user.addresses
  unfold sourceMachine afterArgumentsMachine
  cases out.effect <;> rfl

theorem threads (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64) :
    (machine out count).threads=(CurrentCallPush.preparedMachine before #[]).threads := by
  change (sourceMachine out).threads=(CurrentCallPush.preparedMachine before #[]).threads
  unfold sourceMachine afterArgumentsMachine
  cases out.effect <;> rfl

theorem active (out : CurrentCallEmptyEntryRoot.Output input #[]) (count : UInt64)
    (ready : CurrentCallPush.StackReadiness before #[]) :
    ∃ thread,(machine out count).threads.activeThread?=some thread ∧ thread.topUserRelevantFrame=some 0 := by
  obtain ⟨thread,present,_⟩ := ready
  refine ⟨{thread with topUserRelevantFrame:=some 0},?_,rfl⟩
  rw [threads]
  exact PushThread.cache_top_active (CallEntryFacts.freshRoot before).1 thread 0 present

theorem source_counter (out : CurrentCallEmptyEntryRoot.Output input #[]) :
    (sourceTracker out).global.nextPointerTag=TypedRetagEmpty.successorTag tracker.global.nextPointerTag (fresh input) := by
  unfold sourceTracker afterArgumentsTracker CurrentCallEmptyEntryArguments.nextTracker
  cases out.effect <;> rfl

theorem counter (out : CurrentCallEmptyEntryRoot.Output input #[]) :
    (held out).global.nextPointerTag.value.toNat=tracker.global.nextPointerTag.value.toNat+2 := by
  have first := GenericFunctionEntryNumerics.successor_value tracker.global.nextPointerTag (fresh input)
  have second := GenericFunctionEntryNumerics.successor_value (sourceTracker out).global.nextPointerTag out.room
  rw [held_global]
  change (TypedRetagEmpty.successorTag (sourceTracker out).global.nextPointerTag out.room).value.toNat=_
  rw [second,source_counter,first]

theorem budgets (out : CurrentCallEmptyEntryRoot.Output input #[]) :
    options.place.dynamicFuel=(options.place.dynamicFuel-1)+1 ∧
    options.limits.validation=(options.limits.validation-1)+1 ∧
    limits.callDispatch=(limits.callDispatch-1)+1 ∧
    (held out).global.nextPointerTag.value.toNat+4<2^64 := by
  have lower : 64≤DuplicatePrefixCallSpecification.work before 0 := by unfold DuplicatePrefixCallSpecification.work;omega
  have dynamic := input.machine.resources.dynamicFuel
  have validation := input.machine.resources.configuredFuel.2.2.2
  have dispatch := input.machine.resources.executionFuel.1
  have tagRoom := input.machine.resources.tagRoom
  rw [counter]
  omega


end
end DuplicatePrefix.CurrentCallEmptyEntryNonzeroDispatchState

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyEntryNonzeroDispatchState" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved nonzero dispatcher state dependency {dependency}"
