import duplicate_prefix.S05DiagnosticLenRelease
import duplicate_prefix.LenReturnFromRelease
namespace DuplicatePrefix.S05DiagnosticLenReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open ActualReferenceContext PtrMetadataExecution PtrMetadataReturn GeneralBorrowForestMixedLenBeforeReturn
set_option maxRecDepth 65536
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- The actual diagnostic helper Return; its child11 release is derived internally. -/
theorem step (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions=false) (fuel : Nat) (validationEq : options.limits.validation=fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller helper : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (argument : Immediate Provenance) (facts : ReturnFacts options remaining span helper machine 2 argument)
    (helperLocation : helper.location=.mir ⟨1,1⟩)
    (retval : helper.locals[0]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 2)))),some RootCompilerFacts.usizeLayout⟩)
    (helperRace : helper.extra.dataRace=none)
    (destination : helper.returnPlace.toRuntimePlace=LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout)
    (continuation : helper.returnContinuation=.goto (some 3) .Continue) (varargs : helper.vaList=#[])
    (valid : (11 : MIR.LocalId)<caller.locals.size)
    (live : caller.locals[11].value=.live (.immediate .uninit))
    (cached : caller.locals[11].layout=some RootCompilerFacts.usizeLayout)
    (callerRace : caller.extra.dataRace=none)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (childTree : BorrowTree) (beforeMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (memoryEq : machine.memory=RetagEntry.updatedMemory beforeMemory id entry childTree)
    (held : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (tracked : machine.borrowTracker=some held) (frameTracked : helper.extra.borrowTracker=some borrowFrame)
    (frameOwned : borrowFrame.protectedTags=#[(id,S05DiagnosticFnEntryRead.tag 11)])
    (treeEq : childTree = (S05DiagnosticLenRead.afterRead.newChild Size.ZERO
      (.concrete (S05DiagnosticFnEntryRead.tag 10)) (S05DiagnosticFnEntryRead.tag 11)
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree)
    (protectedEq : held.global.protectedTags = S05DiagnosticLenRelease.protections)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow) :
    ∃ root post,
      ExecutionMachine.step (config options (remaining+1) span) limits ()
        (Storage.withCurrent (frames.push caller) helper machine)=(Storage.withCurrent frames root post,.ok true) ∧
      root={writeFrame caller 11 (.scalar (.fromScalarInt (.ofUInt64 2))) valid with location:=.mir ⟨3,0⟩} ∧
      post.memory=RetagEntry.updatedMemory beforeMemory id entry S05DiagnosticLenRelease.released ∧
      post.borrowTracker=some {held with global:=held.global.endCall borrowFrame} := by
  have complete : childTree.releaseProtector (S05DiagnosticFnEntryRead.tag 11) held.global.protectedTags =
      ⟨S05DiagnosticLenRelease.released,.Released⟩ := by
    rw [treeEq,protectedEq]
    exact S05DiagnosticLenRelease.actual_release
  exact LenReturnFromRelease.step options limits remaining span debugOff fuel validationEq
    frames caller helper machine 2 argument facts helperLocation retval helperRace destination continuation varargs
    valid live cached callerRace id (S05DiagnosticFnEntryRead.tag 11) entry childTree S05DiagnosticLenRelease.released
    beforeMemory memoryEq held borrowFrame tracked frameTracked frameOwned complete ghost shallow
/-- The same physical Return with its entire computed machine exposed. -/
theorem step_state (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (debugOff : options.place.debugAssertions=false) (fuel : Nat) (validationEq : options.limits.validation=fuel+1)
    (frames : Array CompilerFrameContext.ActualFrame) (caller helper : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (argument : Immediate Provenance) (facts : ReturnFacts options remaining span helper machine 2 argument)
    (helperLocation : helper.location=.mir ⟨1,1⟩)
    (retval : helper.locals[0]?=some ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 2)))),some RootCompilerFacts.usizeLayout⟩)
    (helperRace : helper.extra.dataRace=none)
    (destination : helper.returnPlace.toRuntimePlace=LocalPlaces.localRuntimePlace frames.size caller 11 RootCompilerFacts.usizeLayout)
    (continuation : helper.returnContinuation=.goto (some 3) .Continue) (varargs : helper.vaList=#[])
    (valid : (11 : MIR.LocalId)<caller.locals.size)
    (live : caller.locals[11].value=.live (.immediate .uninit))
    (cached : caller.locals[11].layout=some RootCompilerFacts.usizeLayout)
    (callerRace : caller.extra.dataRace=none)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (childTree : BorrowTree) (beforeMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (memoryEq : machine.memory=RetagEntry.updatedMemory beforeMemory id entry childTree)
    (held : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (tracked : machine.borrowTracker=some held) (frameTracked : helper.extra.borrowTracker=some borrowFrame)
    (frameOwned : borrowFrame.protectedTags=#[(id,S05DiagnosticFnEntryRead.tag 11)])
    (treeEq : childTree = (S05DiagnosticLenRead.afterRead.newChild Size.ZERO
      (.concrete (S05DiagnosticFnEntryRead.tag 10)) (S05DiagnosticFnEntryRead.tag 11)
      (Miri.DataStructures.DedupRangeMap.new (Size.ofBytes 2) GeneralBorrowFreshAnchor.sharedState) .Frozen true).tree)
    (protectedEq : held.global.protectedTags = S05DiagnosticLenRelease.protections)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow) :
    let inside : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation := entry.allocation.setExtra childTree}
    let releasedMemory := StackPopRelease.commitTree machine.memory id inside S05DiagnosticLenRelease.released
    ∃ (thread : ThreadRecord), ∃ root post,
      machine.threads.activeThread? = some thread ∧
      ExecutionMachine.step (config options (remaining+1) span) limits ()
        (Storage.withCurrent (frames.push caller) helper machine)=(Storage.withCurrent frames root post,.ok true) ∧
      root={writeFrame caller 11 (.scalar (.fromScalarInt (.ofUInt64 2))) valid with location:=.mir ⟨3,0⟩} ∧
      post.memory=RetagEntry.updatedMemory beforeMemory id entry S05DiagnosticLenRelease.released ∧
      post.borrowTracker=some {held with global:=held.global.endCall borrowFrame} ∧
      post = poppedMachine frames caller helper
        (ActualPopPlan.released (accountedMachine options remaining span machine) releasedMemory held borrowFrame)
        (thread.topUserRelevantFrame.getD (frames.push caller).size) := by
  dsimp only
  have complete : childTree.releaseProtector (S05DiagnosticFnEntryRead.tag 11) held.global.protectedTags =
      ⟨S05DiagnosticLenRelease.released,.Released⟩ := by
    rw [treeEq,protectedEq]
    exact S05DiagnosticLenRelease.actual_release
  let inside : LocalAllocation Provenance BorrowTree MiriMemoryKind := {entry with allocation:=entry.allocation.setExtra childTree}
  have found : machine.memory.live.find? (fun row=>row.1==id)=some (id,inside) := by
    rw [memoryEq]
    exact StackPopRelease.lookup_commit_same beforeMemory id entry childTree
  let releasedMemory := StackPopRelease.commitTree machine.memory id inside S05DiagnosticLenRelease.released
  have plan : StackPopRelease.Plan held.global.protectedTags borrowFrame.protectedTags.toList machine.memory releasedMemory := by
    rw [frameOwned]
    exact StackPopRelease.Plan.live id (S05DiagnosticFnEntryRead.tag 11) inside S05DiagnosticLenRelease.released [] machine.memory _ found complete (.nil _)
  have valid0 : (0 : MIR.LocalId)<helper.locals.size := by rw [facts.size];decide
  have returnedLocal : helper.locals[0]'valid0 =
      ⟨.live (.immediate (.scalar (.fromScalarInt (.ofUInt64 2)))),some RootCompilerFacts.usizeLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans retval)
  have immediate : ∀ slot ∈ helper.locals, ∀ memory, slot.value≠.live (.indirect memory) := by
    apply PtrMetadataComplete.all_direct_three helper.locals facts.size
    · simp only [retval,Option.map_some,PtrMetadataComplete.isDirect]
    · simp only [facts.argument,Option.map_some,PtrMetadataComplete.isDirect]
    · have known := congrArg (Option.map PtrMetadataComplete.isDirect) facts.dead2
      simpa only [Option.map_map,Function.comp_def,Option.map_some,PtrMetadataComplete.isDirect] using known
  obtain ⟨thread,active⟩ := facts.active
  have returned := LenReturn.step_with_plan options limits remaining span debugOff fuel validationEq frames caller helper machine 2
    facts.body helperLocation valid0 (congrArg LocalState.value returnedLocal) (congrArg LocalState.layout returnedLocal) helperRace
    11 valid live cached callerRace destination 3 .Continue continuation immediate varargs held borrowFrame tracked frameTracked
    releasedMemory plan thread active facts.unchecked facts.noGc facts.fixed ghost shallow
  let root : CompilerFrameContext.ActualFrame :=
    {writeFrame caller 11 (.scalar (.fromScalarInt (.ofUInt64 2))) valid with location:=.mir ⟨3,0⟩}
  let post := poppedMachine frames caller helper
    (ActualPopPlan.released (accountedMachine options remaining span machine) releasedMemory held borrowFrame)
    (thread.topUserRelevantFrame.getD (frames.push caller).size)
  have postMemory : post.memory=releasedMemory := by
    unfold post poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have postTracked : post.borrowTracker=some {held with global:=held.global.endCall borrowFrame} := by
    unfold post poppedMachine GenericPopFrame.afterRelevanceAt
    split <;> rfl
  have memoryFinal : releasedMemory=RetagEntry.updatedMemory beforeMemory id entry S05DiagnosticLenRelease.released := by
    change RetagEntry.updatedMemory machine.memory id inside S05DiagnosticLenRelease.released=_
    rw [memoryEq]
    exact RetagEntry.updated_memory_twice beforeMemory id entry childTree S05DiagnosticLenRelease.released
  exact ⟨thread,root,post,active,returned,rfl,postMemory.trans memoryFinal,postTracked,rfl⟩
end
end DuplicatePrefix.S05DiagnosticLenReturn
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.S05DiagnosticLenReturn." then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved diagnostic len return dependency {dependency}"
