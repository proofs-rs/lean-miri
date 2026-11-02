import duplicate_prefix.S03ActiveSameReturnStepBounds
import duplicate_prefix.S03FinalReturnInputBounds
import duplicate_prefix.S03FinalReturnAccountingBounds
import duplicate_prefix.RootZeroCompletePrefix
import duplicate_prefix.RootZeroInvocationState

namespace DuplicatePrefix.S03ZeroCountBodyActiveSameBounds
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S03FinalReturnInputBounds
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Actual count-zero MIR body and Return for a same-allocation active positive
source protector, including the real source release and physical return.
This staged rule takes the return activity after source release; a complete
contract theorem must derive that transport from the installed packet. -/
theorem complete_after_source_activity
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (defaultMode : tracker.retagMode = .Default)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (place : MPlaceTy Provenance) (destination : Destination machine place)
    (returnTag : BorTag) (child selected : UniIndex) (maximum : Option BorTag)
    (returnNode : TreeNode)
    (sourceTag : BorTag) (sourceChild sourceSelected : UniIndex)
    (sourceMaximum : Option BorTag) (sourceOffset sourceLen : UInt64) (sourceNode : TreeNode)
    (sourceTagged : destination.entry.allocation.extra.indexOfTag sourceTag = some sourceChild)
    (sourcePresent : destination.entry.allocation.extra.nodeAt sourceChild = some sourceNode)
    (sourceHidden : sourceNode.isExposed = false)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra tracker.global)
    (sourcePositive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra tracker.global.protectedTags
      (some sourceChild) (some sourceSelected) sourceMaximum sourceOffset sourceLen)
    (sourceDistinct : destination.entry.allocation.extra.roots.toList.Nodup)
    (sourceOrder : ∀ valid : 0 < destination.entry.allocation.extra.roots.size,
      sourceSelected ≠ destination.entry.allocation.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra)
    (sourceShort : destination.entry.allocation.extra.nodes.size < 65536)
    (sourceActivity : GeneralBorrowFreshActiveWithin.ActiveWithin destination.entry.allocation.extra sourceChild .Write
      sourceOffset (sourceOffset+sourceLen))
    (owned : borrowFrame.protectedTags = #[(destination.id,sourceTag),(destination.id,returnTag)])
    (returnTagged : destination.entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : destination.entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (returnEdge : returnNode.parent = some destination.parent)
    (returnHidden : returnNode.isExposed = false)
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame destination.entry.allocation.extra borrowFrame)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra tracker.global)
    (positive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra tracker.global.protectedTags
      (some child) (some selected) maximum destination.offset 1)
    (distinct : destination.entry.allocation.extra.roots.toList.Nodup)
    (order : ∀ valid : 0 < destination.entry.allocation.extra.roots.size,
      selected ≠ destination.entry.allocation.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra)
    (short : destination.entry.allocation.extra.nodes.size < 65536)
    (disjoint : (sourceOffset+sourceLen).toNat ≤ destination.offset.toNat ∨ (destination.offset+1).toNat ≤ sourceOffset.toNat)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin
      (destination.entry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree child .Write
      destination.offset (destination.offset+1))
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (race : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
      some (destination.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < destination.offset.toNat ∨ destination.offset.toNat + 1 ≤ row.1.bytes.toNat)
    (fuel : Nat) (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (source : PreparedContracts.SourceComparator)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (identity : frame.bodyIdentity = RootBody.reflected.body.identity)
    (callee : frame.functionInstance = RootBody.reflected.functionInstance)
    (location : frame.location = .mir ⟨0,0⟩)
    (frameSize : frame.locals.size = 25)
    (live0 : (frame.locals[0]'(by omega)).value = .live (.immediate .uninit))
    (uncached0 : (frame.locals[0]'(by omega)).layout = none)
    (dead3 : (frame.locals[3]'(by omega)).value = .dead)
    (dead4 : (frame.locals[4]'(by omega)).value = .dead)
    (dead5 : (frame.locals[5]'(by omega)).value = .dead)
    (uncached4 : (frame.locals[4]'(by omega)).layout = none)
    (uncached5 : (frame.locals[5]'(by omega)).layout = none)
    (live2 : (frame.locals[2]'(by omega)).value = .live (.immediate (.scalar (.fromScalarInt (.ofUInt64 0)))))
    (cached2 : (frame.locals[2]'(by omega)).layout = some RootCompilerFacts.usizeLayout)
    (noLocalClocks : frame.extra.dataRace = none)
    (returnPlace : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩)
    (continuation : frame.returnContinuation = .stop true)
    (immediateLocals : CopyHelperCleanup.AllImmediate frame)
    (varargs : frame.vaList = #[])
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let cfg := PreparedContracts.actualConfig options () (remaining+1) span
    let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
      ⟨cfg,limits,fun _ _ => True⟩
    ∃ done, SuccessfulTrace.Trace cfg limits (Storage.withCurrent #[] frame machine) done ∧
      ExecutionMachine.step cfg limits () done = (done,.ok false) ∧ done.stack.frames = #[] ∧
      CallSafety.NoErrorsBeforeReturn safety 1 (Storage.withCurrent #[] frame machine) ∧
      CallSafety.NoUBBeforeReturn safety 1 (Storage.withCurrent #[] frame machine) := by
  obtain ⟨result,prefixTrace,fb,fi,ff,fe,frp,frc,fva,fli,fsz,resultLocation,result0,allResult⟩ :=
    RootZeroCompletePrefix.reaches_return options limits remaining span source debugOff fuel validationFuel
      frame machine sourceBody identity callee location frameSize live0 uncached0 dead3 dead4 dead5 uncached4 uncached5
      live2 cached2 noLocalClocks immediateLocals tracker enabled defaultMode ghost shallow unchecked noGc fixed
  let first := RootZeroCompleteState.tick options remaining span machine
  let current := RootZeroCompleteState.tick options remaining span first
  let d1 := S03FinalReturnAccountingBounds.destination options remaining span frame machine place destination
  let d2 := S03FinalReturnAccountingBounds.destination options remaining span frame first place d1
  have valid0 : (0 : MIR.LocalId) < result.locals.size := by rw [fsz];decide
  have slot0 : result.locals[0] = ⟨.live (.immediate (.scalar (.fromBool true))),some RootCompilerFacts.boolLayout⟩ :=
    Option.some.inj ((Array.getElem?_eq_getElem valid0).symm.trans result0)
  have currentGhost : current.user.payload.ghost = false := by
    dsimp only [current,first]
    rw [RootZeroCompleteState.tick_ghost,RootZeroCompleteState.tick_ghost]
    exact ghost
  have currentShallow : current.user.payload.validation = .Shallow := by
    dsimp only [current,first]
    rw [RootZeroCompleteState.tick_shallow,RootZeroCompleteState.tick_shallow]
    exact shallow
  have firstFlags := RootZeroCompleteState.tick_flags options remaining span machine
  have secondFlags := RootZeroCompleteState.tick_flags options remaining span first
  have currentUnchecked := secondFlags.1.trans (firstFlags.1.trans unchecked)
  have currentNoGc := secondFlags.2.trans (firstFlags.2.trans noGc)
  have fields1 := RootZeroInvocationState.tick_fields options remaining span machine
  have fields2 := RootZeroInvocationState.tick_fields options remaining span first
  have currentExtras : current.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
      some (destination.id,⟨none,sync⟩) := by
    rw [fields2.2.2.2.2.2.2,fields1.2.2.2.2.2.2]
    exact extras
  obtain ⟨updated,returned,_,_,_⟩ := S03ActiveSameReturnStepBounds.step options limits remaining span
    result current tracker borrowFrame enabled (by rw [fe];exact frameTracked) place d2
    sourceTag sourceChild sourceSelected sourceMaximum
    sourceOffset sourceLen sourceNode sourceTagged sourcePresent sourceHidden sourceRuntime sourcePositive
    sourceDistinct sourceOrder sourceShort sourceActivity returnTag child selected maximum returnNode
    returnTagged returnPresent returnSame returnEdge returnHidden owned hiddenFrame
    runtime positive distinct order short disjoint activity thread active race
    (by rw [fields2.2.2.2.2.2.1,fields1.2.2.2.2.2.1];exact backend)
    currentGhost currentShallow sync currentExtras outside true fuel debugOff validationFuel
    (fb.trans sourceBody) resultLocation valid0 (by rw [slot0]) (by rw [slot0]) (by rw [fe];exact noLocalClocks)
    (by rw [frp];exact returnPlace) (frc.trans continuation) allResult (fva.trans varargs)
    currentUnchecked currentNoGc fixed
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span result current
  let sourceReleased := (destination.entry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree accounted.memory destination.id destination.entry sourceReleased
  let released := (sourceReleased.releaseProtector returnTag tracker.global.protectedTags).tree
  let after := S04FinalReturnVariantsInput.afterPop #[] result accounted tracker borrowFrame priorMemory destination.id destination.entry released
    (thread.topUserRelevantFrame.getD 0)
  let done := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  have last : ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent #[] result current) = (done,.ok true) := returned
  have trace := SuccessfulTrace.append prefixTrace (SuccessfulTrace.Trace.next last (.refl _))
  let safety : CallSafety.Context MiriMemoryKind Machine.RootUser Unit Unit Miri.ABI.ExternAbi Unit :=
    ⟨PreparedContracts.actualConfig options () (remaining+1) span,limits,fun _ _ => True⟩
  have entry : CallSafety.IsCallEntry 1 (Storage.withCurrent #[] frame machine) := by
    simp [CallSafety.IsCallEntry,CallSafety.frameDepth,Storage.withCurrent]
  have exited : CallSafety.pastCallBoundary 1 done := by
    change (0 : Nat) < 1
    decide
  exact ⟨done,trace,rfl,rfl,SuccessfulTrace.no_errors safety 1 _ done entry trace exited,
    SuccessfulTrace.no_ub safety 1 _ done entry trace exited⟩

end
end DuplicatePrefix.S03ZeroCountBodyActiveSameBounds

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S03ZeroCountBodyActiveSameBounds.complete_after_source_activity) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved zero-count active same body dependency {dependency}"
