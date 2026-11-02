import duplicate_prefix.GeneralBorrowReadProtectorReleaseEndCall
import duplicate_prefix.LenReturnFromReleaseRuntime
namespace DuplicatePrefix.GeneralBorrowRawSharedLenReturnRuntime
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.Concurrency
open ActualReferenceContext PtrMetadataExecution PtrMetadataReturn GeneralBorrowForestMixedLenBeforeReturn
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Actual shared len helper Return from current raw resources. Actual release
and singleton endCall are derived internally, including successor Read capability. -/
theorem from_current (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
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
    (childTree : BorrowTree) (beforeMemory : MemoryState Provenance BorrowTree MiriMemoryKind)
    (memoryEq : machine.memory=RetagEntry.updatedMemory beforeMemory id entry childTree)
    (held : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (tracked : machine.borrowTracker=some held) (frameTracked : helper.extra.borrowTracker=some borrowFrame)
    (frameOwned : borrowFrame.protectedTags=#[(id,tag)])
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts childTree held.global)
    (anchor selected : UniIndex) (maximum : Option BorTag) (offset : UInt64)
    (positive : GeneralBorrowReadRowRange.Positive childTree held.global.protectedTags anchor selected maximum offset len)
    (node : TreeNode) (present : childTree.nodeAt anchor = some node)
    (sameTag : node.tag = tag) (hidden : node.isExposed = false)
    (tagged : childTree.indexOfTag tag = some anchor) (distinct : childTree.roots.toList.Nodup)
    (order : ∀ valid : 0 < childTree.roots.size, selected ≠ childTree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder childTree)
    (short : childTree.nodes.size < 65536)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin childTree anchor .Read offset (offset+len))
    (rootCache : RootCache frames machine) (race : machine.dataRace=none)
    (ghost : machine.user.payload.ghost=false) (shallow : machine.user.payload.validation=.Shallow) :
    let released := (childTree.releaseProtector tag held.global.protectedTags).tree
    ∃ root post,
      ExecutionMachine.step (config options (remaining+1) span) limits ()
        (Storage.withCurrent (frames.push caller) helper machine)=(Storage.withCurrent frames root post,.ok true) ∧
      root={writeFrame caller 11 (.scalar (.fromScalarInt (.ofUInt64 len))) valid with location:=.mir ⟨3,0⟩} ∧
      post.memory=RetagEntry.updatedMemory beforeMemory id entry released ∧
      post.borrowTracker=some {held with global:=held.global.endCall borrowFrame} ∧
      DuplicatePrefixBorrowContract.RuntimeFacts released (held.global.endCall borrowFrame) ∧
      Nonempty (GeneralBorrowReadRowRange.Positive released (held.global.endCall borrowFrame).protectedTags anchor selected maximum offset len) ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin released anchor .Write offset (offset+len) ∧
      GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span machine post ∧
      (frames=#[] → ∃ thread,post.threads.activeThread?=some thread ∧ thread.topUserRelevantFrame=some 0)
 := by
  let released := (childTree.releaseProtector tag held.global.protectedTags).tree
  have frameEq : borrowFrame = (({} : FrameState).addProtector id tag) := by
    cases borrowFrame
    simp_all [FrameState.addProtector]
  obtain ⟨done,runtimeAfter,positiveAfter,activityAfter,absent,other,shape,capacity⟩ :=
    GeneralBorrowReadProtectorReleaseEndCall.release_end_call childTree held.global runtime id tag anchor selected maximum offset len
      positive node present sameTag hidden tagged distinct order short activity
  have complete : childTree.releaseProtector tag held.global.protectedTags = ⟨released,.Released⟩ := by
    cases equation : childTree.releaseProtector tag held.global.protectedTags with
    | mk tree status =>
      simp only [equation] at done
      cases done
      unfold released
      rw [equation]
  obtain ⟨root,post,step,rootEq,memoryAfter,trackerAfter,machineFacts,topFacts⟩ := LenReturnFromReleaseRuntime.step options limits remaining span debugOff fuel validationEq
    frames caller helper machine len argument facts helperLocation retval helperRace destination continuation varargs
    valid live cached callerRace id tag entry childTree released beforeMemory memoryEq held borrowFrame tracked frameTracked frameOwned complete rootCache race ghost shallow
  refine ⟨root,post,step,rootEq,memoryAfter,trackerAfter,?_,?_,activityAfter,machineFacts,topFacts⟩
  · simpa only [frameEq] using runtimeAfter
  · simpa only [frameEq] using positiveAfter
end
end DuplicatePrefix.GeneralBorrowRawSharedLenReturnRuntime
