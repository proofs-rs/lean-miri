import duplicate_prefix.S04FinalReturnWildcardDriver

namespace DuplicatePrefix.S04FinalReturnWildcard
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S04FinalReturnVariantsInput S04FinalReturnWildcardInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Transport the permission-free wildcard physical packet across actual
beforeTerminator accounting, retaining the real inverse-map binding. -/
def accounted_destination (options : EvalConfigurationCore.Options) (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (before : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (place : MPlaceTy Provenance) (input : Destination before place) :
    Destination (S04FinalReturnRuleAccounting.machine options remaining span frame before) place where
  pointer := input.pointer
  physicalPointer := input.physicalPointer
  layout := input.layout
  aligned := input.aligned
  id := input.id
  entry := input.entry
  base := input.base
  offset := input.offset
  capacity := input.capacity
  live := input.live
  pointerAddress := input.pointerAddress
  nonnull := input.nonnull
  addressFits := input.addressFits
  bounds := input.bounds
  size := input.size
  bytes := input.bytes
  mutable := input.mutable
  maskValid := input.maskValid
  maskLength := input.maskLength
  pointerBounds := input.pointerBounds
  borrowSize := input.borrowSize
  wildcard := input.wildcard
  cachedBase := by
    rw [(S04FinalReturnRuleAccounting.metadata options remaining span frame before).1]
    exact input.cachedBase
  mode := by
    rw [(S04FinalReturnRuleAccounting.metadata options remaining span frame before).1]
    exact input.mode
  exposed := by
    rw [(S04FinalReturnRuleAccounting.metadata options remaining span frame before).1]
    exact input.exposed
  geometry := by
    rw [(S04FinalReturnRuleAccounting.metadata options remaining span frame before).1]
    exact input.geometry

/-- Actual configured Return step at duplicate_prefix's original return block.
Source accounting is executed first; its effects are carried through the real
local read, protector release/pop, physical return copy, validation and cleanup.
All premises describe the pre-step frame, physical data and borrow state.
This is a local final-step theorem, not formation of the preceding body. -/
theorem step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (place : MPlaceTy Provenance) (destination : Destination machine place)
    (returnTag : BorTag) (child : UniIndex)
    (returnNode : TreeNode)
    (argument : ArgumentProtection machine.memory borrowFrame destination.id destination.entry returnTag)
    (returnTagged : destination.entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : destination.entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (parentless : returnNode.parent = none)
    (leaf : returnNode.children = #[])
    (returnHidden : returnNode.isExposed = false)
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame destination.entry.allocation.extra borrowFrame)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra tracker.global)
    (positive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra tracker.global.protectedTags
      (some child) (some child) (some returnTag) destination.offset 1)
    (distinct : destination.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound destination.entry.allocation.extra returnTag)
    (notPrimary : ∀ valid : 0 < destination.entry.allocation.extra.roots.size, destination.entry.allocation.extra.roots[0] ≠ child)
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
    (value : Bool) (fuel : Nat)
    (debugOff : options.place.debugAssertions = false)
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
    let released := (destination.entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
    let after := S04FinalReturnVariantsInput.afterPop #[] frame accounted tracker borrowFrame argument.priorMemory destination.id destination.entry released
      (thread.topUserRelevantFrame.getD 0)
    ∃ updated, ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits ()
      (Storage.withCurrent #[] frame machine) =
      (CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated,.ok true) ∧
      updated.byteSize = destination.entry.allocation.byteSize ∧
      updated.len = destination.entry.allocation.len ∧ updated.mutability = .Mut := by
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let initial := Storage.withCurrent #[] frame machine
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span frame machine
  let current := Storage.withCurrent #[] frame accounted
  let currentDestination := accounted_destination options remaining span frame machine place destination
  have metadata := S04FinalReturnRuleAccounting.metadata options remaining span frame machine
  have currentExtras : accounted.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = some (destination.id,⟨none,sync⟩) := by
    rw [metadata.2.2.2.2]
    exact extras
  obtain ⟨updated,returned,size,length,mutable⟩ := S04FinalReturnWildcardDriver.return_effect options limits remaining span
    frame accounted tracker borrowFrame enabled frameTracked place currentDestination
    returnTag child returnNode argument
    returnTagged returnPresent returnSame parentless leaf returnHidden hiddenFrame runtime positive distinct order exposed notPrimary short activity
    thread active race (by rw [metadata.2.2.2.1];exact backend) (by rw [metadata.2.1];exact ghost)
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
end DuplicatePrefix.S04FinalReturnWildcard
