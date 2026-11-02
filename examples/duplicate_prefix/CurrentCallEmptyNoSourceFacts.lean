import duplicate_prefix.DuplicatePrefixCallModel
import duplicate_prefix.CurrentCallEmptySourceArguments
import duplicate_prefix.PositiveRootInstalledFrame
import duplicate_prefix.RootZeroCompletePrefix
namespace DuplicatePrefix.CurrentCallEmptyNoSourceFacts
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateCurrentJointCall CanonicalConfigFacts ActualReferenceContext RootFrameData EmptyRootArguments
open CurrentCallEmptyTypedEntry TypedBorrowSteps
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
/-- One common current metadata boundary for an actual source-protector-free
copy followed by Bool protection. Equality of user data retains types, origins,
addresses, extras and caches together; it is not a post-operation premise. -/
structure Checkpoint (before : Before) (frames : Array CompilerFrameContext.ActualFrame)
    (old : MachineHooks.BorrowState) (machine : Before) (global : GlobalState) (boolTag : BorTag) : Prop where
  user : machine.user=(CurrentCallPush.preparedMachine before frames).user
  lookup : GlobalAddressLiveErrorExclusion.lookup machine.memory=GlobalAddressLiveErrorExclusion.lookup before.memory
  counter : global.nextPointerTag.value.toNat=old.global.nextPointerTag.value.toNat+2
  flags : global.protectedTags=old.global.protectedTags.insert boolTag .StrongProtector
  rootTags : global.rootPointerTags=old.global.rootPointerTags
  trackedTags : global.trackedPointerTags=old.global.trackedPointerTags

variable (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (before : Before) (tracker : MachineHooks.BorrowState)
    (argument : DuplicatePrefixSliceArgument.Argument) (effect : Effect options before tracker argument)
    (root : RootFrame) (count : UInt64)
    (id : AllocId) (tag : BorTag)

def args : RootFrame := RootArgumentsTwo.result
  (CurrentCallEmptySourceArguments.doneRoot effect
    remaining span root {}) count

def frame := CallEntryFacts.doneRootFrame
  {registeredFrame (atSpan (args options remaining span before tracker argument effect root count) ⟨601⟩).frame {} id tag
    with location:=.unwinding ⟨559⟩}

def value : Immediate Provenance := (DuplicatePrefixSliceArgument.rawValue (config options remaining span).access.runtime.base argument 0 ActualReferenceMetadata.reference).imm

variable (noSource : effect.allocation=none)
include noSource

/-- Only local storage is compared here. The actual frame has ONE Bool
protector; this equality makes no source-child or source-family assertion. -/
theorem locals_eq :
    (frame options remaining span before tracker argument effect root count id tag).locals=
      (PositiveRootInstalledFrame.installed root (value options remaining span argument) count {} id tag id tag).locals := by
  simp only [frame,args,CurrentCallEmptySourceArguments.doneRoot,CurrentCallEmptyTypedEntry.resultFrame,
    noSource,CurrentCallEmptyTypedEntry.copied,
    CurrentCallEmptyReferenceValidation.writtenFrame,PositiveRootInstalledFrame.installed,
    PositiveRootArguments.firstDone,PositiveRootArguments.protectedRoot,CallEntryFacts.doneRootFrame,
    CallEntryFacts.liveSlot,registeredFrame,TypedRetagEntry.frameWithBorrow,RootArgumentsTwo.result,
    firstLive,firstCache,live,write,cache,atSpan,LocalOperands.cachedLayoutFrame,value,Array.set_set,
    Array.getElem_set_self,i1]

theorem metadata :
    let f:=frame options remaining span before tracker argument effect root count id tag
    f.body=root.frame.body ∧ f.bodyIdentity=root.frame.bodyIdentity ∧ f.functionInstance=root.frame.functionInstance ∧
    f.returnContinuation=root.frame.returnContinuation ∧ f.returnPlace=root.frame.returnPlace ∧ f.vaList=root.frame.vaList ∧
    f.extra.dataRace=root.frame.extra.dataRace ∧ f.extra.borrowTracker=some (({} : FrameState).addProtector id tag) ∧
    f.location=.mir ⟨0,0⟩ := by
  simp only [frame,args,CurrentCallEmptySourceArguments.doneRoot,CurrentCallEmptyTypedEntry.resultFrame,
    noSource,CurrentCallEmptyTypedEntry.copied,
    CurrentCallEmptyReferenceValidation.writtenFrame,CallEntryFacts.doneRootFrame,CallEntryFacts.liveSlot,
    registeredFrame,TypedRetagEntry.frameWithBorrow,RootArgumentsTwo.result,
    firstLive,firstCache,live,write,cache,atSpan,LocalOperands.cachedLayoutFrame]
  repeat' constructor

/-- Real count-zero root control from the actual source-protector-free empty frame. Its
single Bool protector and original return place are preserved literally. -/
theorem zero_prefix
    (limits : ExecutionMachine.Limits)
    (raw : root.frame.locals=Array.replicate 25 (⟨.dead,none⟩ : LocalState Provenance LocalLayout))
    (machine : Before) (model : DuplicatePrefixCallModel.Model options remaining span machine)
    (fuel : Nat) (fuelEq : options.limits.validation=fuel+1) :
    let f:=frame options remaining span before tracker argument effect root 0 id tag
    ∃ result : CompilerFrameContext.ActualFrame,
      SuccessfulTrace.Trace (config options (remaining+1) span) limits (Storage.withCurrent #[] f machine)
        (Storage.withCurrent #[] result (RootZeroCompleteState.tick options remaining span (RootZeroCompleteState.tick options remaining span machine))) ∧
      result.body=RootBody.reflected.body.body ∧ result.bodyIdentity=RootBody.reflected.body.identity ∧
      result.functionInstance=RootBody.reflected.functionInstance ∧ result.locals.size=25 ∧ result.location=.mir ⟨10,0⟩ ∧
      result.locals[0]?=some ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ ∧
      result.returnPlace=f.returnPlace ∧ result.extra=f.extra ∧ result.returnContinuation=f.returnContinuation ∧
      result.vaList=f.vaList ∧ CopyHelperCleanup.AllImmediate result := by
  let f:=frame options remaining span before tracker argument effect root 0 id tag
  have locals:=locals_eq options remaining span before tracker argument effect root 0 id tag noSource
  have size : f.locals.size=25 := (congrArg Array.size locals).trans (PositiveRootInstalledFrame.size _ _ _ _ _ _ _ _)
  have cells (index : Fin 25) := PositiveRootInstalledFrame.slot_option root raw (value options remaining span argument) 0 {} id tag id tag index
  rw [←locals] at cells
  have get (index : Fin 25) := Option.some.inj ((Array.getElem?_eq_getElem (show index.val<f.locals.size by rw [size];exact index.isLt)).symm.trans (cells index))
  have immediate : CopyHelperCleanup.AllImmediate f := by
    change ∀ current∈f.locals,∀ memory,current.value≠.live (.indirect memory)
    rw [locals]
    exact PositiveRootInstalledFrame.immediate _ raw _ _ _ _ _ _ _
  obtain ⟨body,identity,callee,continuation,returnPlace,varargs,clocks,borrow,location⟩ := metadata options remaining span before tracker argument effect root 0 id tag noSource
  obtain ⟨current,enabled,mode⟩:=model.defaultTracker
  let source:=DuplicatePrefixCallModel.sourceComparator options remaining span machine model
  obtain ⟨result,trace,resultBody,resultIdentity,resultCallee,extra,returnPlace,continuation,varargs,_,resultSize,returnLocation,returnValue,all⟩ :=
    RootZeroCompletePrefix.reaches_return options limits remaining span source model.debugOff fuel fuelEq f machine
      (body.trans root.body) (identity.trans root.identity) (callee.trans root.callee) location size
      (by simpa using congrArg LocalState.value (get ⟨0,by decide⟩))
      (by simpa using congrArg LocalState.layout (get ⟨0,by decide⟩))
      (by simpa using congrArg LocalState.value (get ⟨3,by decide⟩))
      (by simpa using congrArg LocalState.value (get ⟨4,by decide⟩))
      (by simpa using congrArg LocalState.value (get ⟨5,by decide⟩))
      (by simpa using congrArg LocalState.layout (get ⟨4,by decide⟩))
      (by simpa using congrArg LocalState.layout (get ⟨5,by decide⟩))
      (by simpa using congrArg LocalState.value (get ⟨2,by decide⟩))
      (by simpa using congrArg LocalState.layout (get ⟨2,by decide⟩))
      (clocks.trans root.noClocks) immediate current enabled mode model.ghostOff model.shallow model.unchecked model.noGc model.fixedScheduler
  exact ⟨result,trace,resultBody.trans (body.trans root.body),resultIdentity.trans (identity.trans root.identity),resultCallee.trans (callee.trans root.callee),resultSize,returnLocation,returnValue,returnPlace,extra,continuation,varargs,all⟩

end
end DuplicatePrefix.CurrentCallEmptyNoSourceFacts
