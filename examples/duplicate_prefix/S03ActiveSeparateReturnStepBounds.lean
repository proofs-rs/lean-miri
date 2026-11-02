import duplicate_prefix.S03ActiveSeparateReturnDriverBounds
import duplicate_prefix.S03FinalReturnAccountingBounds
import duplicate_prefix.S04FinalReturnVariants

namespace DuplicatePrefix.S03ActiveSeparateReturnStepBounds
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S03FinalReturnInputBounds S04FinalReturnVariantsInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- The original ExecutionMachine Return step for a distinct active source.
All release, copy, validation and stop operations execute from current facts. -/
theorem step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (place : MPlaceTy Provenance) (destination : Destination machine place)
    (sourceId : AllocId) (sourceEntry : LocalAllocation Provenance BorrowTree MiriMemoryKind)
    (separate : destination.id ≠ sourceId)
    (sourceLive : machine.memory.live.find? (fun row => row.1 == sourceId) = some (sourceId,sourceEntry))
    (sourceTag : BorTag) (sourceChild sourceSelected : UniIndex)
    (sourceMaximum : Option BorTag) (sourceOffset sourceLen : UInt64) (sourceNode : TreeNode)
    (sourceTagged : sourceEntry.allocation.extra.indexOfTag sourceTag = some sourceChild)
    (sourcePresent : sourceEntry.allocation.extra.nodeAt sourceChild = some sourceNode)
    (sourceHidden : sourceNode.isExposed = false)
    (sourceRuntime : DuplicatePrefixBorrowContract.RuntimeFacts sourceEntry.allocation.extra tracker.global)
    (sourcePositive : DuplicatePrefixBorrowAuthorization.Positive sourceEntry.allocation.extra tracker.global.protectedTags
      (some sourceChild) (some sourceSelected) sourceMaximum sourceOffset sourceLen)
    (sourceDistinct : sourceEntry.allocation.extra.roots.toList.Nodup)
    (sourceOrder : ∀ valid : 0 < sourceEntry.allocation.extra.roots.size,
      sourceSelected ≠ sourceEntry.allocation.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceEntry.allocation.extra)
    (sourceShort : sourceEntry.allocation.extra.nodes.size < 65536)
    (sourceActivity : GeneralBorrowFreshActiveWithin.ActiveWithin sourceEntry.allocation.extra sourceChild .Write
      sourceOffset (sourceOffset+sourceLen))
    (returnTag : BorTag) (child selected : UniIndex) (maximum : Option BorTag)
    (returnNode : TreeNode)
    (returnTagged : destination.entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : destination.entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (returnEdge : returnNode.parent = some destination.parent)
    (returnHidden : returnNode.isExposed = false)
    (owned : borrowFrame.protectedTags = #[(sourceId,sourceTag),(destination.id,returnTag)])
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame destination.entry.allocation.extra borrowFrame)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra tracker.global)
    (positive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra tracker.global.protectedTags
      (some child) (some selected) maximum destination.offset 1)
    (distinct : destination.entry.allocation.extra.roots.toList.Nodup)
    (order : ∀ valid : 0 < destination.entry.allocation.extra.roots.size,
      selected ≠ destination.entry.allocation.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra)
    (short : destination.entry.allocation.extra.nodes.size < 65536)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin destination.entry.allocation.extra child .Write
      destination.offset (destination.offset+1))
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (race : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) =
      some (destination.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync,
      row.1.bytes.toNat < destination.offset.toNat ∨ destination.offset.toNat + 1 ≤ row.1.bytes.toNat)
    (value : Bool) (fuel : Nat) (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (sourceBody : frame.body = RootBody.reflected.body.body)
    (location : frame.location = .mir ⟨10,0⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar (.fromBool value))))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.boolLayout)
    (noLocalClocks : frame.extra.dataRace = none)
    (returnPlace : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩)
    (continuation : frame.returnContinuation = .stop true)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory))
    (varargs : frame.vaList = #[])
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let accounted := S04FinalReturnRuleAccounting.machine options remaining span frame machine
    let sourceReleased := (sourceEntry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree
    let priorMemory := StackPopRelease.commitTree accounted.memory sourceId sourceEntry sourceReleased
    let released := (destination.entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
    let after := S04FinalReturnVariantsInput.afterPop #[] frame accounted tracker borrowFrame priorMemory
      destination.id destination.entry released (thread.topUserRelevantFrame.getD 0)
    ∃ updated, ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent #[] frame machine) =
      (CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated,.ok true) ∧
      updated.byteSize = destination.entry.allocation.byteSize ∧
      updated.len = destination.entry.allocation.len ∧ updated.mutability = .Mut := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let initial := Storage.withCurrent #[] frame machine
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span frame machine
  let current := Storage.withCurrent #[] frame accounted
  let currentDestination := S03FinalReturnAccountingBounds.destination options remaining span frame machine place destination
  have metadata := S04FinalReturnRuleAccounting.metadata options remaining span frame machine
  have currentExtras : accounted.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,sync⟩) := by
    rw [metadata.2.2.2.2]
    exact extras
  have currentSourceLive : accounted.memory.live.find? (fun row => row.1 == sourceId) =
      some (sourceId,sourceEntry) := by
    change machine.memory.live.find? (fun row => row.1 == sourceId) = _
    exact sourceLive
  obtain ⟨updated,returned,size,length,mutable⟩ := S03ActiveSeparateReturnDriverBounds.return_effect
    options limits remaining span frame accounted tracker borrowFrame enabled frameTracked place currentDestination
    sourceId sourceEntry separate currentSourceLive sourceTag sourceChild sourceSelected sourceMaximum sourceOffset sourceLen sourceNode
    sourceTagged sourcePresent sourceHidden sourceRuntime sourcePositive sourceDistinct sourceOrder sourceShort sourceActivity
    returnTag child selected maximum returnNode returnTagged returnPresent returnSame returnEdge returnHidden owned
    hiddenFrame runtime positive distinct order short activity thread active race
    (by rw [metadata.2.2.2.1];exact backend) (by rw [metadata.2.1];exact ghost)
    (by rw [metadata.2.2.1];exact shallow) sync currentExtras outside value fuel debugOff validationFuel
    sourceBody location valid0 live0 cached0 noLocalClocks returnPlace continuation immediateLocals varargs
  have accounting := SourceControl.before_terminator config limits () initial
    (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  have accounting' : (ExecutionMachine.stepHooks config limits).beforeTerminator () initial = (current,.ok ()) := accounting
  let block := RootBody.reflected.body.body.basicBlocks[10]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[10]? = some block := by rw [sourceBody];simp [block]
  have noStatement : block.statements[0]? = none := by with_unfolding_all rfl
  have kind : block.terminator.kind = .Return := by with_unfolding_all rfl
  refine ⟨updated,?_,size,length,mutable⟩
  exact GenericCallReturn.return_step_exact config limits () initial current _ frame ⟨10,0⟩ block
    (by simp [initial,Storage.withCurrent,Stack.currentFrame?]) location blockAt noStatement kind accounting' returned

end
end DuplicatePrefix.S03ActiveSeparateReturnStepBounds

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S03ActiveSeparateReturnStepBounds.step) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved active separate Return step dependency {dependency}"
