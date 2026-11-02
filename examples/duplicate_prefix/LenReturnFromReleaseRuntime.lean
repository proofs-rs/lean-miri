import duplicate_prefix.LenReturn
import duplicate_prefix.GeneralBorrowForestMixedLenCallReturnRuntime
namespace DuplicatePrefix.LenReturnFromReleaseRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open ActualReferenceContext PtrMetadataExecution PtrMetadataReturn GeneralBorrowForestMixedLenBeforeReturn
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

theorem step (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions=false) (fuel : Nat) (validationEq : options.limits.validation=fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller helper : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser) (len : UInt64)
    (argument : Immediate Provenance) (facts : ReturnFacts options remaining span helper machine len argument)
    (helperLocation : helper.location=.mir ⟨1,1⟩)
    (retval : helper.locals[0]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩)
    (helperRace : helper.extra.dataRace=none)
    (destination : helper.returnPlace.toRuntimePlace=LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout)
    (continuation : helper.returnContinuation=.goto (some 3) .Continue) (varargs : helper.vaList=#[])
    (valid : (11 : MIR.LocalId)<caller.locals.size)
    (live : caller.locals[11].value=.live (.immediate .uninit))
    (cached : caller.locals[11].layout=some RootCompilerFacts.usizeLayout)
    (callerRace : caller.extra.dataRace=none)
    (id : AllocId) (tag : BorTag) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (childTree released : BorrowTree) (beforeMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (memoryEq : machine.memory=RetagEntry.updatedMemory beforeMemory id entry childTree)
    (held : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (tracked : machine.borrowTracker=some held) (frameTracked : helper.extra.borrowTracker=some borrowFrame)
    (frameOwned : borrowFrame.protectedTags=#[(id,tag)])
    (complete : childTree.releaseProtector tag held.global.protectedTags=⟨released,.Released⟩)
    (rootCache : RootCache frames machine) (race : machine.dataRace=none)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow) :
    ∃ root post,
      ExecutionMachine.step (config options (remaining+1) span) limits ()
        (Storage.withCurrent (frames.push caller) helper machine)=(Storage.withCurrent frames root post,.ok true) ∧
      root={writeFrame caller 11 (.scalar (.fromScalarInt (.ofUInt64 len))) valid with location:=.mir ⟨3,0⟩} ∧
      post.memory=RetagEntry.updatedMemory beforeMemory id entry released ∧
      post.borrowTracker=some {held with global:=held.global.endCall borrowFrame} ∧
      GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span machine post ∧
      (frames=#[] → ∃ thread,post.threads.activeThread?=some thread ∧ thread.topUserRelevantFrame=some 0) := by
  let inside : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation:=entry.allocation.setExtra childTree}
  have found : machine.memory.live.find? (fun row=>row.1==id)=some (id,inside) := by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_same beforeMemory id entry childTree
  let releasedMemory := StackPopRelease.commitTree machine.memory id inside released
  have plan : StackPopRelease.Plan held.global.protectedTags borrowFrame.protectedTags.toList machine.memory releasedMemory := by
    rw [frameOwned]
    exact StackPopRelease.Plan.live id tag inside released [] machine.memory _ found complete (.nil _)
  have valid0 : (0 : MIR.LocalId)<helper.locals.size := by rw [facts.size];decide
  have returnedLocal : helper.locals[0]'valid0 =
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 len)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans retval)
  have immediate : ∀ slot ∈ helper.locals, ∀ memory, slot.value≠.live (.indirect memory) := by
    apply PtrMetadataComplete.all_direct_three helper.locals facts.size
    · simp only [retval,Option.map_some,PtrMetadataComplete.isDirect]
    · simp only [facts.argument,Option.map_some,PtrMetadataComplete.isDirect]
    · have known := congrArg (Option.map PtrMetadataComplete.isDirect) facts.dead2
      simpa only [Option.map_map,Function.comp_def,Option.map_some,PtrMetadataComplete.isDirect] using known
  obtain ⟨thread,active⟩ := facts.active
  have returned := LenReturn.step_with_plan options limits remaining span debugOff fuel validationEq frames caller helper machine len
    facts.body helperLocation valid0 (congrArg LocalState.value returnedLocal) (congrArg LocalState.layout returnedLocal) helperRace
    11 valid live cached callerRace destination 3 .Continue continuation immediate varargs held borrowFrame tracked frameTracked
    releasedMemory plan thread active facts.unchecked facts.noGc facts.fixed ghost shallow
  let root : CompilerFrameContext.ActualFrame :=
    {writeFrame caller 11 (.scalar (.fromScalarInt (.ofUInt64 len))) valid with location:=.mir ⟨3,0⟩}
  let post := poppedMachine frames caller helper
    (ActualPopPlan.released (accountedMachine options remaining span machine) releasedMemory held borrowFrame)
    (thread.topUserRelevantFrame.getD (frames.push caller).size)
  have postMemory : post.memory=releasedMemory := by
    unfold post poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have postTracked : post.borrowTracker=some {held with global:=held.global.endCall borrowFrame} := by
    unfold post poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have memoryFinal : releasedMemory=RetagEntry.updatedMemory beforeMemory id entry released := by
    change RetagEntry.updatedMemory machine.memory id inside released=_
    rw [memoryEq]
    exact RetagEntry.updated_memory_twice beforeMemory id entry childTree released
  have postGhost : post.user.payload.ghost=false := by
    simp only [post,popped_user,ActualPopPlan.released,accounted_ghost];exact ghost
  have postShallow : post.user.payload.validation=.Shallow := by
    simp only [post,popped_user,ActualPopPlan.released,accounted_validation];exact shallow
  have postFlags :
      ((config options (remaining+1) span).terminators.getControl post.user).checkedArithmetic=false ∧
      ((config options (remaining+1) span).terminators.getControl post.user).gcInterval=0 := by
    simp only [post,popped_user,ActualPopPlan.released]
    exact ⟨(RootZeroCompleteState.tick_flags options remaining span machine).1.trans facts.unchecked,
      (RootZeroCompleteState.tick_flags options remaining span machine).2.trans facts.noGc⟩
  have postFixed : post.threads.fixedScheduling=true := by
    unfold post poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> exact facts.fixed
  have tickData : (RootZeroCompleteState.tick options remaining span machine).user.addresses=machine.user.addresses ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.types=machine.user.payload.payload.user.types ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras ∧
      (RootZeroCompleteState.tick options remaining span machine).user.payload.payload.user.backend=machine.user.payload.payload.user.backend := by
    unfold RootZeroCompleteState.tick SourceControl.accounted
    rw [(CanonicalConfigFacts.actual_fields options () (remaining+1) span).terminators]
    exact ⟨rfl,rfl,rfl,rfl⟩
  have postData : post.user.addresses=machine.user.addresses ∧
      post.user.payload.payload.user.types=machine.user.payload.payload.user.types ∧
      post.user.payload.payload.user.runtime.extras=machine.user.payload.payload.user.runtime.extras ∧
      post.user.payload.payload.user.backend=machine.user.payload.payload.user.backend := by
    simpa only [post,popped_user,ActualPopPlan.released,RootZeroCompleteState.tick,accountedMachine] using tickData
  have runtime : GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span machine post := by
    refine ⟨postGhost,postShallow,?_,postData.1,postData.2.1,postData.2.2.1,
      postData.2.2.2.trans facts.backend,postFlags.1,postFlags.2,postFixed,?_⟩
    · unfold post poppedMachine GenericPopFrame.afterRelevanceAt
      split <;> exact race
    · let releasedMachine := ActualPopPlan.released (accountedMachine options remaining span machine) releasedMemory held borrowFrame
      have known : releasedMachine.threads.activeThread?=some thread := active
      unfold post poppedMachine GenericPopFrame.afterRelevanceAt
      split
      · exact ⟨_,MetadataOutputFacts.relevance_active (frames.push caller) helper releasedMachine thread known⟩
      · exact ⟨thread,known⟩
  have cache : frames=#[] → ∃ nextThread,post.threads.activeThread?=some nextThread ∧ nextThread.topUserRelevantFrame=some 0 := by
    intro empty
    subst frames
    obtain ⟨cacheThread,cacheActive,cacheBound⟩ := rootCache.bound rfl
    have same : thread=cacheThread := Option.some.inj (active.symm.trans cacheActive)
    have bound : ∀ index,thread.topUserRelevantFrame=some index → index<2 := by rw [same];exact cacheBound
    let releasedMachine := ActualPopPlan.released (accountedMachine options remaining span machine) releasedMemory held borrowFrame
    have known : releasedMachine.threads.activeThread?=some thread := active
    unfold post poppedMachine GenericPopFrame.afterRelevanceAt
    have pairTop : FrameRelevance.computeTop ⟨#[caller,helper]⟩ 1=some 0 := by
      simp [FrameRelevance.computeTop,List.range_succ,List.range_zero,Id.run]
      split <;> rfl
    split
    · exact ⟨_,MetadataOutputFacts.relevance_active #[caller] helper releasedMachine thread known,pairTop⟩
    · rename_i notCurrent
      cases cache : thread.topUserRelevantFrame with
      | none => simp [cache] at notCurrent
      | some index =>
        have bounded := bound index cache
        have neq : index≠1 := by simpa [cache] using notCurrent
        have zero : index=0 := by omega
        exact ⟨thread,known,cache.trans (congrArg some zero)⟩
  exact ⟨root,post,returned,rfl,postMemory.trans memoryFinal,postTracked,runtime,cache⟩
end
end DuplicatePrefix.LenReturnFromReleaseRuntime
