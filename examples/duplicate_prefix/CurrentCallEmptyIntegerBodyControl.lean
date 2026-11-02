import duplicate_prefix.CurrentCallEmptyIntegerFacts
import duplicate_prefix.S03EmptyIntegerBody
namespace DuplicatePrefix.CurrentCallEmptyIntegerBodyControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- The existing actual empty-integer helper path consumes the real post-entry
frame. Only two further tags are allocated; no tree or protector is changed. -/
theorem to_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (oldTracker : MachineHooks.BorrowState) (root : RootFrame) (address count : UInt64) (id : AllocId) (tag : BorTag)
    (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (machine : Before) (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    (nonzero : address≠0) (countNonzero : count≠0)
    (tagRoomNext : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (budget : Nat) (dispatchFuel : limits.callDispatch=budget+1)
    (thread : Miri.Concurrency.ThreadRecord) (activeThread : machine.threads.activeThread?=some thread)
    (topZero : thread.topUserRelevantFrame=some 0) :
    let frame:=CurrentCallEmptyIntegerFacts.frame options remaining span before oldTracker root address count id tag
    ∃ result : CompilerFrameContext.ActualFrame,
      ∃ finalMachine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser,
      ∃ finalTracker : MachineHooks.BorrowState,
      SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
        (Storage.withCurrent #[] frame machine) (Storage.withCurrent #[] result finalMachine) ∧
      result.body = frame.body ∧ result.bodyIdentity = frame.bodyIdentity ∧ result.functionInstance = frame.functionInstance ∧
      result.extra = frame.extra ∧ result.returnPlace = frame.returnPlace ∧ result.returnContinuation = frame.returnContinuation ∧
      result.vaList = frame.vaList ∧ result.localsIdentity = frame.localsIdentity ∧ result.locals.size = 25 ∧
      result.location = .mir ⟨10,0⟩ ∧
      result.locals[0]? = some ⟨.live (.immediate (.scalar (.fromBool false))),some RootCompilerFacts.boolLayout⟩ ∧
      CopyHelperCleanup.AllImmediate result ∧
      finalMachine.memory = machine.memory ∧
      finalMachine.borrowTracker = some finalTracker ∧ finalTracker.retagMode = tracker.retagMode ∧
      finalTracker.global = {tracker.global with nextPointerTag := finalTracker.global.nextPointerTag} ∧
      finalTracker.global.nextPointerTag.value.toNat = tracker.global.nextPointerTag.value.toNat+2 ∧
      finalMachine.user.payload.ghost = false ∧ finalMachine.user.payload.validation = .Shallow ∧
      finalMachine.dataRace = none ∧ finalMachine.threads.fixedScheduling = true ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).checkedArithmetic = false ∧
      ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl finalMachine.user).gcInterval = 0 ∧
      finalMachine.user.addresses = machine.user.addresses ∧
      finalMachine.user.payload.payload.user.types = machine.user.payload.payload.user.types ∧
      finalMachine.user.payload.payload.user.backend = machine.user.payload.payload.user.backend ∧
      finalMachine.user.payload.payload.user.runtime.extras = machine.user.payload.payload.user.runtime.extras ∧
      (∃ finalThread, finalMachine.threads.activeThread? = some finalThread) := by
  let frame:=CurrentCallEmptyIntegerFacts.frame options remaining span before oldTracker root address count id tag
  have locals:=CurrentCallEmptyIntegerFacts.locals_eq options remaining span before oldTracker root address count id tag
  have size : frame.locals.size=25 := (congrArg Array.size locals).trans (PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _)
  have cells (index : Fin 25) := PositiveRootInstalledFrame.slot_option root raw (CurrentCallEmptyIntegerFacts.value options remaining span address) count {} id tag id tag index
  rw [←locals] at cells
  have get (index : Fin 25) := Option.some.inj ((Array.getElem?_eq_getElem (show index.val<frame.locals.size by rw [size];exact index.isLt)).symm.trans (cells index))
  have all : CopyHelperCleanup.AllImmediate frame := by
    change ∀current∈frame.locals,∀memory,current.value≠.live (.indirect memory)
    rw [locals]
    exact PositiveRootInstalledFrame.immediate _ raw _ _ _ _ _ _ _
  obtain ⟨body,identity,callee,continuation,returnPlace,varargs,clocks,borrow,location⟩ :=
    CurrentCallEmptyIntegerFacts.metadata options remaining span before oldTracker root address count id tag
  obtain ⟨current,enabled,mode⟩:=model.defaultTracker
  have same : current=tracker:=Option.some.inj (enabled.symm.trans tracked)
  subst current
  have fresh : tracker.global.nextPointerTag.value<18446744073709551615 := UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)
  have unused : ∀index (valid:index<frame.locals.size),7≤index→index≤12→frame.locals[index]'valid=⟨.dead,none⟩ := by
    intro index valid lower upper
    have row:=get ⟨index,by omega⟩
    simpa only [show ¬(14=index ∨13=index ∨6=index ∨0=index) by omega,show ¬2=index by omega,show ¬1=index by omega,ite_false] using row
  exact S03EmptyIntegerBody.to_return options limits remaining span (DuplicatePrefixCallModel.sourceComparator options remaining span machine model)
    model.nullComparator model.preciseOff model.implicitOff model.debugOff dynamicFuel validityFuel dynamicEq validityEq frame machine address count nonzero countNonzero size
    (by simpa [CurrentCallEmptyIntegerFacts.value,DuplicatePrefixSliceArgument.rawValue] using congrArg LocalState.value (get ⟨1,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨1,by decide⟩))
    (by simpa using congrArg LocalState.value (get ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨2,by decide⟩))
    (by simpa using congrArg LocalState.value (get ⟨3,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨3,by decide⟩))
    (by simpa using congrArg LocalState.value (get ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.value (get ⟨5,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨4,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨5,by decide⟩)) unused
    (body.trans root.body) (identity.trans root.identity) (callee.trans root.callee) location (clocks.trans root.noClocks) all tracker tracked mode fresh
    model.ghostOff model.shallow model.unchecked model.noGc model.fixedScheduler model.metadata
    (DuplicatePrefixTypeCacheOrigins.slice_not_constructed _ model.metadata origins) budget dispatchFuel tagRoomNext model.noDataRace model.noBackend thread activeThread topZero
    (by simpa using congrArg LocalState.value (get ⟨0,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨0,by decide⟩))
    (by simpa using congrArg LocalState.value (get ⟨13,by decide⟩))
    (by simpa using congrArg LocalState.layout (get ⟨13,by decide⟩))
end
end DuplicatePrefix.CurrentCallEmptyIntegerBodyControl
