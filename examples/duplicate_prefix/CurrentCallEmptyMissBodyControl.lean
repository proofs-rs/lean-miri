import duplicate_prefix.CurrentCallEmptyMissFacts
import duplicate_prefix.CurrentCallEmptyEntryNonzeroBodyMiss
namespace DuplicatePrefix.CurrentCallEmptyMissBodyControl
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section
/-- The existing actual wildcard-query-miss helper path consumes the real post-entry
frame. Only two further tags are allocated; no tree or protector is changed. -/
theorem to_return
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (oldTracker : MachineHooks.BorrowState) (root : RootFrame) (address count : UInt64) (id : AllocId) (tag : BorTag)
    (initialMiss : before.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup before.memory)=.ok none)
    (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (machine : Before) (tracker : MachineHooks.BorrowState) (tracked : machine.borrowTracker=some tracker)
    (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (origins : DuplicatePrefixTypeCacheOrigins.Origins machine.user.payload.payload.user.types)
    (nonzero : address≠0) (countNonzero : count≠0)
    (addressMode : machine.user.addresses.provenanceMode≠.strict)
    (miss : machine.user.addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup machine.memory)=.ok none)
    (tagRoomNext : tracker.global.nextPointerTag.value.toNat+1<18446744073709551615)
    (dynamicFuel validityFuel : Nat) (dynamicEq : options.place.dynamicFuel=dynamicFuel+1) (validityEq : options.limits.validation=validityFuel+1)
    (budget : Nat) (dispatchFuel : limits.callDispatch=budget+1)
    (thread : Miri.Concurrency.ThreadRecord) (activeThread : machine.threads.activeThread?=some thread)
    (topZero : thread.topUserRelevantFrame=some 0) :
    let frame:=CurrentCallEmptyMissFacts.frame options remaining span before oldTracker root address count id tag initialMiss
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
  let effect : CurrentCallEmptyTypedEntry.Effect options before oldTracker
      (.pointer (Pointer.new .wildcard (Size.ofBytes address))) := .miss address initialMiss
  let first:=CurrentCallEmptySourceArguments.doneRoot effect remaining span root {}
  have fresh : tracker.global.nextPointerTag.value<18446744073709551615 :=
    UInt64.lt_iff_toNat_lt.mpr (by change tracker.global.nextPointerTag.value.toNat<18446744073709551615;omega)
  have targetEq : (config options remaining span).access.runtime.base=(config options (remaining+1) span).access.runtime.base := by
    rw [actual_access_runtime options () remaining span,actual_access_runtime options () (remaining+1) span]
  have representation : CurrentCallEmptyEntryFrame.adjusted effect remaining span=
      (RetagReferencePlace.sliceValue (config options (remaining+1) span).access.runtime.base
        (Pointer.new .wildcard (Size.ofBytes address)) 0 ActualReferenceMetadata.reference).imm := by
    simp only [CurrentCallEmptyEntryFrame.adjusted,CurrentCallEmptyTypedEntry.Effect.output,effect,
      CurrentCallEmptyTypedEntry.Effect.allocation,DuplicatePrefixSliceArgument.rawValue,targetEq]
  exact CurrentCallEmptyEntryNonzeroBodyMiss.miss_from_installed effect limits remaining span root first raw rfl {} id tag
    machine model origins tracker tracked address count nonzero countNonzero representation fresh addressMode miss
    dynamicFuel validityFuel budget dynamicEq validityEq dispatchFuel tagRoomNext thread activeThread topZero
end
end DuplicatePrefix.CurrentCallEmptyMissBodyControl
