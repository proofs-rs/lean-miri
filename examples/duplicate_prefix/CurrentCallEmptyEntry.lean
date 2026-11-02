import duplicate_prefix.CurrentCallEmptyEntryBool
import duplicate_prefix.CurrentCallEntry

/-! Actual full empty-source Call.initStackFrame. Source copy, Bool protection,
frame installation and their exact effects are composed from ORIGINAL Proposed.
This is conditional entry coverage, not an ordinary-admission or whole-root claim. -/
namespace DuplicatePrefix.CurrentCallEmptyEntry
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open Miri.Input Miri.Interpreter
open CandidateStableCallOwnership CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext
open RootFrameData EmptyRootArguments TypedBorrowSteps ReferenceBorrowDriver
open CurrentCallEmptyTypedEntry CurrentCallEmptyEntryBool
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

def sourceBorrow {options before tracker argument} (effect : Effect options before tracker argument) (initial : FrameState) : FrameState :=
  match effect.allocation with
  | none => initial
  | some id => initial.addProtector id tracker.global.nextPointerTag

private theorem result_borrow {options before tracker argument} (effect : Effect options before tracker argument)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (frame : CompilerFrameContext.ActualFrame)
    (initial : FrameState) (borrow : frame.extra.borrowTracker = some initial) (localId : MIR.LocalId) (valid : localId < frame.locals.size) :
    (resultFrame effect remaining span frame initial localId valid).extra.borrowTracker = some (sourceBorrow effect initial) := by
  cases effect <;> first | exact borrow | rfl

private theorem return_abi (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (state : RootState) :
    (ExecutionMachine.callHooks (config options remaining span) limits).checkArgumentCompat ()
      RootCompilerFacts.rootAbi.ret RootCompilerFacts.rootAbi.ret state = .ok true state := by
  change (config options remaining span).calls.compiler.checkArgumentCompat () _ _ _ = _
  rw [(CanonicalConfigFacts.actual_fields options () remaining span).callCompiler]
  exact CallEntryFacts.root_return_argument_compat _ options.compatibilityBudget _

private theorem tail_of_steps (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (root : RootFrame) (machine : Before)
    (place : MPlaceTy Provenance) (after protectedState : RootState)
    (protect : (ExecutionMachine.callHooks (config options remaining span) limits).protectArgument () place
      (Storage.withCurrent frames (atSpan root ⟨601⟩).frame machine) = .ok () protectedState)
    (finish : RootEntryFinish.finish (ExecutionMachine.callHooks (config options remaining span) limits) protectedState = .ok () after) :
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

/-- One actual full empty-source entry, universally in UInt64 count. Every
finite source case and both argument copies run under one FnEntry scope; Bool
protection and full frame installation follow on the same actual machine. -/
theorem invoke (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState) (argument : DuplicatePrefixSliceArgument.Argument)
    (place : MPlaceTy Provenance) (call : CallLoans) (data : Identities)
    (input : CurrentCallAdmission.Proposed options limits remaining span before tracker argument 0 place call data)
    (frames : Array CompilerFrameContext.ActualFrame) (stackReady : CurrentCallPush.StackReadiness before frames)
    (memoryReady : CurrentCallBoolProtection.ProfileMemoryReadiness before call) (count : UInt64) :
    let machine := CurrentCallPush.preparedMachine before frames
    let initialRoot := CurrentCallEntry.root before frames place input.machine.settings.noDataRace
    let prepared := firstLive initialRoot
    let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
    ∃ effect : Effect options machine tracker argument,∃ firstDone : RootFrame,
    ∃ physical : CandidateCurrentBoolUninitWrite.PhysicalWindow
      (afterArgumentsMachine effect fresh remaining span frames prepared.frame {} 1 (prepared.valid i1)) place,
    ∃ room : (afterArgumentsTracker effect fresh).global.nextPointerTag.value < 18446744073709551615,
    ∃ output : GeneralBorrowForestFnEntry.Output,∃ updated : Allocation Provenance BorrowTree,
    let argsRoot := RootArgumentsTwo.result firstDone count
    let changed := atSpan argsRoot ⟨601⟩
    let currentMachine := afterArgumentsMachine effect fresh remaining span frames prepared.frame {} 1 (prepared.valid i1)
    let currentTracker := afterArgumentsTracker effect fresh
    let protectedFrame := registeredFrame changed.frame (sourceBorrow effect {}) physical.id currentTracker.global.nextPointerTag
    let retagged := ReturnProtection.borrowedState frames changed.frame (sourceBorrow effect {}) currentMachine currentTracker room physical.id physical.entry output.child.tree
    let finalMachine : Before := {retagged.machine with memory := {retagged.machine.memory with live :=
      ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push (physical.id,{physical.entry with allocation := updated}))}}
    let finalFrame := CallEntryFacts.doneRootFrame {protectedFrame with location := .unwinding ⟨559⟩}
    firstDone.frame = resultFrame effect remaining span prepared.frame {} 1 (prepared.valid i1) ∧
    Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) ()
      RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
      #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0),.Copy (second count)]
      false (CurrentCallArguments.destination place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState) =
      .ok () (Storage.withCurrent frames finalFrame finalMachine) ∧
    finalFrame.returnPlace = CurrentCallArguments.destination place ∧
    physical.id = call.returnId ∧ physical.offset = UInt64.ofNat call.returnOffset ∧
    DuplicatePrefixBorrowContract.RuntimeFacts updated.extra output.global ∧
    CurrentCallBoolProtection.ProfileMemoryReadiness finalMachine call ∧
    CandidateCallBindings.WindowBinding finalMachine physical.pointer call.returnId call.returnOffset 1 ∧
    DuplicatePrefixTypeCacheOrigins.Origins finalMachine.user.payload.payload.user.types ∧
    updated.byteSize = physical.entry.allocation.byteSize ∧ updated.len = physical.entry.allocation.len ∧
    AllocationCopy.snapshot updated = AllocationCopy.snapshot physical.entry.allocation := by
  let machine := CurrentCallPush.preparedMachine before frames
  let transported := CurrentCallPush.prepared_input input frames
  let initialRoot := CurrentCallEntry.root before frames place input.machine.settings.noDataRace
  let prepared := firstLive initialRoot
  let fresh := CandidateCurrentLiveRuntime.tag_room options limits remaining before tracker 0 input.machine.resources
  obtain ⟨effect,firstDone,frameEq,returnEq,arguments⟩ := CurrentCallEmptyEntryArguments.arguments options limits remaining span machine tracker argument place call data
    transported frames (CallEntryFacts.freshRoot before).2 count
  let argsRoot := RootArgumentsTwo.result firstDone count
  let changed := atSpan argsRoot ⟨601⟩
  have initialBorrow : prepared.frame.extra.borrowTracker = some ({} : FrameState) :=
    RootEntryFrame.raw_borrow machine (CurrentCallArguments.destination place) (CallEntryFacts.freshRoot before).2 tracker transported.machine.state.enabled
  have frameBorrow : changed.frame.extra.borrowTracker = some (sourceBorrow effect {}) := by
    change firstDone.frame.extra.borrowTracker = some (sourceBorrow effect {})
    rw [frameEq]
    exact result_borrow effect remaining span prepared.frame {} initialBorrow 1 (prepared.valid i1)
  obtain ⟨ctx⟩ := ActualRetagContext.exists_context options (remaining+1) span input.machine.settings.preciseOff input.machine.settings.implicitOff
  obtain ⟨physical,room,output,updated,idEq,offsetEq,protect,runtime,ready,binding,bytes,length,snapshot,origins⟩ := protect_after_arguments
    transported (memoryReady.prepared frames) effect ctx frames prepared.frame {} 1 (prepared.valid i1) changed.frame (sourceBorrow effect {}) frameBorrow
  let currentMachine := afterArgumentsMachine effect fresh remaining span frames prepared.frame {} 1 (prepared.valid i1)
  let currentTracker := afterArgumentsTracker effect fresh
  let protectedFrame := registeredFrame changed.frame (sourceBorrow effect {}) physical.id currentTracker.global.nextPointerTag
  let retagged := ReturnProtection.borrowedState frames changed.frame (sourceBorrow effect {}) currentMachine currentTracker room physical.id physical.entry output.child.tree
  let finalMachine : Before := {retagged.machine with memory := {retagged.machine.memory with live :=
    ((retagged.machine.memory.live.filter fun row => row.1 != physical.id).push (physical.id,{physical.entry with allocation := updated}))}}
  have dead : ∀ id : Fin 25,id.val ≠ 1 → id.val ≠ 2 →
      (protectedFrame.locals[id.val]'(by simpa only [protectedFrame,registeredFrame,TypedRetagEntry.frameWithBorrow,changed,atSpan] using argsRoot.valid id)).value = .dead := by
    intro id ne1 ne2
    have rawLocals := RootEntryFrame.raw_locals machine (CurrentCallArguments.destination place) (CallEntryFacts.freshRoot before).2
    have preparedSlot : prepared.frame.locals[id.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simp only [prepared,firstLive,firstCache,RootFrameData.live,RootFrameData.write,RootFrameData.cache,RootFrameData.atSpan,
        LocalOperands.cachedLayoutFrame,Array.getElem?_set,i1,Ne.symm ne1,ite_false]
      change initialRoot.frame.locals[id.val]? = _
      rw [show initialRoot.frame.locals = Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout) from rawLocals]
      simp [id.isLt]
    have firstSlot : firstDone.frame.locals[id.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      rw [frameEq]
      change (resultFrame effect remaining span prepared.frame {} 1 (prepared.valid i1)).locals[id.val]? = _
      rw [CurrentCallEmptyEntryArguments.result_other_local effect remaining span prepared.frame {} 1 (prepared.valid i1) id.val ne1]
      exact preparedSlot
    have found : argsRoot.frame.locals[id.val]? = some (⟨.dead,none⟩ : LocalState Provenance LocalLayout) := by
      simpa only [argsRoot,RootArgumentsTwo.result,RootFrameData.write,RootFrameData.live,RootFrameData.cache,RootFrameData.atSpan,
        LocalOperands.cachedLayoutFrame,Array.getElem?_set,ne2,Ne.symm ne2,ite_false,i2] using firstSlot
    exact congrArg LocalState.value (Option.some.inj ((Array.getElem?_eq_getElem (argsRoot.valid id)).symm.trans found))
  have finish := RootEntryFinish.actual_finish options limits (remaining+1) span frames protectedFrame finalMachine
    argsRoot.body argsRoot.size (dead ⟨0,by decide⟩ (by decide) (by decide)) (dead ⟨6,by decide⟩ (by decide) (by decide))
    (dead ⟨13,by decide⟩ (by decide) (by decide)) (dead ⟨14,by decide⟩ (by decide) (by decide)) argsRoot.noClocks
  have tail := tail_of_steps options limits (remaining+1) span frames argsRoot currentMachine place _ _ protect finish
  change (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits).withRetagMode () .FnEntry
      (RootCallCore.argumentBody (ExecutionMachine.callHooks (PreparedContracts.actualConfig options () (remaining+1) span) limits)
        (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0) (second count))
      (Storage.withCurrent frames initialRoot.frame machine) =
      .ok (2,2) (Storage.withCurrent frames argsRoot.frame currentMachine) at arguments
  have push := CurrentCallPush.push options (remaining+1) span limits input.machine.settings.debugOff before frames (CurrentCallArguments.destination place) stackReady
  have rawEq : CallEntryFacts.rawPushedState frames before (CurrentCallArguments.destination place) = Storage.withCurrent frames initialRoot.frame machine := rfl
  change (ExecutionMachine.callHooks (config options (remaining+1) span) limits).pushRaw () RootBody.reflected.functionInstance RootBody.reflected.body
    (.memory place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState) = .ok () (CallEntryFacts.rawPushedState frames before (.memory place)) at push
  change CallEntryFacts.rawPushedState frames before (.memory place) = Storage.withCurrent frames initialRoot.frame machine at rawEq
  have getFrame := CallEntryLocals.get_frame options limits (remaining+1) span frames initialRoot.frame machine
  have setFrame := CallEntryLocals.set_frame options limits (remaining+1) span frames initialRoot.frame initialRoot.frame machine
  have preamble : initialRoot.frame.location = .unwinding ⟨559⟩ := rfl
  have trackNone : initialRoot.frame.trackCallerArg = none := rfl
  have unchanged : {initialRoot.frame with trackCallerArg := none} = initialRoot.frame := by rw [←trackNone]
  refine ⟨effect,firstDone,physical,room,output,updated,frameEq,?_,returnEq,idEq,offsetEq,runtime,ready,binding,origins,bytes,length,snapshot⟩
  change Call.initStackFrame (ExecutionMachine.callHooks (config options (remaining+1) span) limits) () RootBody.reflected.functionInstance RootBody.reflected.body RootCompilerFacts.rootAbi
    #[.Copy (DuplicatePrefixSliceArgument.first (config options remaining span).access.runtime.base argument 0),.Copy (second count)]
    false (.memory place) (.stop true) (⟨⟨frames⟩,before⟩ : RootState) = _
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
  rw [arguments]
  dsimp only
  exact tail

end
end DuplicatePrefix.CurrentCallEmptyEntry

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CurrentCallEmptyEntry." ||
        name.toString.startsWith "_private.duplicate_prefix.CurrentCallEmptyEntry." then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty full entry dependency {dependency}"
