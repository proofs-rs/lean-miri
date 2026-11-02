import duplicate_prefix.CurrentCallCheckpointAsMutExecution
import duplicate_prefix.AsMutReturnFromReleaseRuntime
namespace DuplicatePrefix.CurrentCallCheckpointAsMutReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.Interpreter Miri.MIR Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallResourceNormalization
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section
variable {options : EvalConfigurationCore.Options} {limits : ExecutionMachine.Limits} {remaining : Nat} {span : PreparedContracts.FixedSpanQuery}
  {before : DuplicatePrefixCallSpecification.Before} {tracker : MachineHooks.BorrowState} {id : AllocId} {offset len : UInt64}
  {entry : LocalAllocation Provenance BorrowTree MiriMemoryKind} {caller : CompilerFrameContext.ActualFrame}
  {base : UInt64} {parentTag : BorTag} {fresh : tracker.global.nextPointerTag.value<18446744073709551615}
  {valid15 : (15 : MIR.LocalId)<caller.locals.size}
  (seed : CurrentCallCheckpointAsMutExecution.Helper options limits remaining span before tracker id offset len entry caller base parentTag fresh valid15)

def releasedTree : BorrowTree:=(seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).tree
def held : MachineHooks.BorrowState:={tracker with global:=seed.output.global}
def postTracker : MachineHooks.BorrowState:={tracker with global:=seed.output.global.endCall seed.output.frame}

def value : Scalar Provenance:=Scalar.fromPointer
  (PreparedContracts.actualConfig options () (remaining+1) span).access.runtime.base
  (Pointer.new (.concrete id seed.output.tag) (Size.ofBytes (base+offset)))

structure Returned where
  root : CompilerFrameContext.ActualFrame
  machine : DuplicatePrefixCallSpecification.Before
  trace : SuccessfulTrace.Trace (PreparedContracts.actualConfig options () (remaining+1) span) limits
    (Storage.withCurrent #[] caller before) (Storage.withCurrent #[] root machine)
  rootEq : root={AsMutPtrReturn.writeFrame (AsMutUncachedCall.cachedCaller caller valid15) 15
    (.scalar (value seed)) seed.callerValid with location:=.mir ⟨7,0⟩}
  memory : machine.memory=RetagEntry.updatedMemory before.memory id entry (releasedTree seed)
  tracked : machine.borrowTracker=some (postTracker seed)
  flags : GeneralBorrowForestMixedLenCallReturnRuntime.RuntimeFacts options remaining span seed.machine machine
  active : ∃ thread,machine.threads.activeThread?=some thread ∧thread.topUserRelevantFrame=some 0
  sourceLive : machine.memory.live.find? (fun row=>row.1==id)=some (id,{entry with allocation:=entry.allocation.setExtra (releasedTree seed)})

private theorem released_pair (result : BorrowTree.ProtectorReleaseResult) (done : result.status=.Released) :
    result=⟨result.tree,.Released⟩ := by
  cases result
  cases done
  rfl

/-- Execute the actual mutable helper's release, whole-frame endCall and pop,
returning its raw child pointer to the SAME caller at root7. -/
theorem of_release (done : (seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags).status=.Released) (debug : options.place.debugAssertions=false) (fuel : Nat) (validation : options.limits.validation=fuel+1) :
    Nonempty (Returned seed) := by
  have complete : seed.output.child.tree.releaseProtector seed.output.tag seed.output.global.protectedTags=
      ⟨releasedTree seed,.Released⟩:=
    released_pair _ done
  obtain ⟨root,post,step,rootEq,memory,tracked,flags,active⟩:=AsMutReturnFromReleaseRuntime.step
    options limits remaining span debug fuel validation #[] (AsMutUncachedCall.cachedCaller caller valid15)
    seed.helper seed.machine (value seed)
    seed.body seed.size seed.argument seed.argumentAt seed.dead2 seed.dead3 seed.dead4 seed.runtime seed.location
    seed.returned seed.clocks seed.destination seed.continuation seed.varargs seed.callerValid seed.callerLive seed.callerCached seed.callerClocks
    id seed.output.tag entry seed.output.child.tree (releasedTree seed) before.memory seed.memory
    (held seed) seed.output.frame seed.tracked seed.borrow seed.frameOwned complete seed.cache
    seed.runtime.race seed.runtime.ghost seed.runtime.shallow
  refine ⟨{
    root:=root,machine:=post,trace:=SuccessfulTrace.append seed.trace (.next step (.refl _)),rootEq:=rootEq,
    memory:=memory,tracked:=tracked,flags:=flags,active:=active rfl,sourceLive:=?_}⟩
  rw [memory]
  exact StackPopRelease.lookup_commit_same before.memory id entry _

end
end DuplicatePrefix.CurrentCallCheckpointAsMutReturn
open Lean Elab Command in
run_cmd do
  for (name,_) in (←getEnv).constants.toList do
    if name.toString.contains "CurrentCallCheckpointAsMutReturn" then
      for dependency in (←collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved common AsMut return dependency {dependency}"
