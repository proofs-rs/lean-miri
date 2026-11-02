import duplicate_prefix.S04FinalReturnRuleAccounting
import duplicate_prefix.RootPhysicalReturnSupport
import duplicate_prefix.RootZeroBranch

namespace DuplicatePrefix.S04FinalReturnRuleDriver
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S04FinalReturnInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Original source Return driver at the fixed duplicate_prefix return block:
actual local read, same-allocation protector pop, generalized physical
copyReturn, cleanup and stop continuation. No successful suboperation is a
premise; the current body-state metadata remains explicit. -/
theorem return_effect
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (place : MPlaceTy Provenance) (destination : Destination machine place)
    (zeroTag returnTag : BorTag) (zeroIndex child selected : UniIndex) (maximum : Option BorTag)
    (zeroNode returnNode : TreeNode)
    (zeroTagged : destination.entry.allocation.extra.indexOfTag zeroTag = some zeroIndex)
    (zeroPresent : destination.entry.allocation.extra.nodeAt zeroIndex = some zeroNode)
    (zeroHidden : zeroNode.isExposed = false)
    (quiet : S04ReturnReleaseInactive.Quiescent destination.entry.allocation.extra zeroIndex)
    (returnTagged : destination.entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : destination.entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (returnEdge : returnNode.parent = some destination.parent)
    (returnHidden : returnNode.isExposed = false)
    (owned : borrowFrame.protectedTags = #[(destination.id,zeroTag),(destination.id,returnTag)])
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
    (varargs : frame.vaList = #[]) :
    let released := (destination.entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
    let after := afterPop #[] frame machine tracker borrowFrame destination.id destination.entry released
      (thread.topUserRelevantFrame.getD 0)
    ∃ updated, ControlFlow.returnFromCurrentFrame
      (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () (remaining+1) span) limits) () false
      (Storage.withCurrent #[] frame machine) =
      (CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated,.ok ()) ∧
      updated.byteSize = destination.entry.allocation.byteSize ∧
      updated.len = destination.entry.allocation.len ∧ updated.mutability = .Mut := by
  obtain ⟨pop,afterRuntime,⟨parentPositive⟩⟩ := S04ReturnReleasePop.pop_same_allocation
    options limits (remaining+1) span #[] frame machine tracker borrowFrame enabled frameTracked
    destination.id destination.entry destination.live zeroTag returnTag zeroIndex child destination.parent selected maximum
    zeroNode returnNode destination.offset zeroTagged zeroPresent zeroHidden quiet returnTagged returnPresent
    returnSame returnEdge returnHidden owned hiddenFrame runtime positive distinct order short activity thread active
  have ownedReturn : (destination.id,returnTag) ∈ borrowFrame.protectedTags.toList := by rw [owned];simp
  obtain ⟨_,_,_,shape,capacity⟩ := S04ReturnReleaseParent.release_to_parent
    destination.entry.allocation.extra tracker.global borrowFrame runtime destination.id returnTag child destination.parent
    selected maximum destination.offset positive returnNode returnPresent returnSame returnEdge returnHidden returnTagged
    ownedReturn hiddenFrame distinct order short activity
  let released := (destination.entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
  let next := after_release destination #[] frame tracker borrowFrame released
    (thread.topUserRelevantFrame.getD 0) shape capacity selected maximum parentPositive
  let after := afterPop #[] frame machine tracker borrowFrame destination.id destination.entry released
    (thread.topUserRelevantFrame.getD 0)
  have fields := afterPop_fields #[] frame machine tracker borrowFrame destination.id destination.entry released
    (thread.topUserRelevantFrame.getD 0)
  have nextRuntime : DuplicatePrefixBorrowContract.RuntimeFacts next.entry.allocation.extra next.tracker.global := afterRuntime
  have nextDistinct : next.entry.allocation.extra.roots.toList.Nodup := by
    change released.roots.toList.Nodup
    rw [congrArg BorrowTree.roots shape]
    exact distinct
  have nextOrder : ∀ valid : 0 < next.entry.allocation.extra.roots.size,
      ∀ chosen, next.selectedRoot = some chosen → chosen ≠ next.entry.allocation.extra.roots[0] →
        GeneralBorrowWildcardParentTagOrder.ParentTagOrder next.entry.allocation.extra := by
    intro valid chosen equal different
    have same : selected = chosen := Option.some.inj equal
    subst chosen
    change 0 < released.roots.size at valid
    change selected ≠ released.roots[0] at different
    have rawRoots := congrArg BorrowTree.roots shape
    have rawNodes := congrArg BorrowTree.nodes shape
    have roots : released.roots = destination.entry.allocation.extra.roots := rawRoots
    have nodes : released.nodes = destination.entry.allocation.extra.nodes := rawNodes
    have initial : GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra :=
      order (by simpa only [roots] using valid) (by simpa only [roots] using different)
    change GeneralBorrowWildcardParentTagOrder.ParentTagOrder released
    unfold GeneralBorrowWildcardParentTagOrder.ParentTagOrder
    rw [nodes]
    exact initial
  have nextShort : next.entry.allocation.extra.nodes.size < 65536 := by
    change released.nodes.size < 65536
    rw [congrArg BorrowTree.nodes shape]
    exact short
  have nextExtras : after.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == next.id) =
      some (next.id,⟨none,sync⟩) := by
    change after.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = _
    rw [fields.1]
    exact extras
  obtain ⟨updated,copied,size,length,mutable⟩ := S04FinalReturnRuleCopy.from_current
    (options := options) limits (remaining := remaining) span after place next nextRuntime nextDistinct nextOrder nextShort
    destination.tag destination.concrete (by rw [fields.2];exact race)
    (by rw [fields.1];exact backend) (by rw [fields.1];exact ghost) (by rw [fields.1];exact shallow)
    sync nextExtras outside value fuel debugOff validationFuel frame.returnPlace returnPlace
  let config := PreparedContracts.actualConfig options () (remaining+1) span
  let control := GenericCallReturn.sourceControl config limits
  let before := Storage.withCurrent #[] frame machine
  let final := CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated
  let result : OpTy Provenance := ⟨.immediate (.scalar (.fromBool value)),RootCompilerFacts.boolLayout⟩
  have read : control.returnOperand () before = (before,.ok result) :=
    PrimitiveCallReturn.read_current_return options limits (remaining+1) span #[] frame machine
      RootCompilerFacts.boolLayout (.scalar (.fromBool value)) valid0 live0 cached0 RootGenericBoolWrite.bool_sized
      noLocalClocks ghost
  have cleanup := RootPhysicalReturnSupport.cleanup_actual_stop options limits (remaining+1) span final frame
    continuation immediateLocals varargs
  let block := RootBody.reflected.body.body.basicBlocks[10]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[10]? = some block := by rw [sourceBody];simp [block]
  have normal : block.cleanup = false := by with_unfolding_all rfl
  have empty : final.stack.frames = #[] := rfl
  have returned := RootPhysicalReturnSupport.normal_stop control () before before after final frame ⟨10,0⟩ block result
    (by simp [before,Storage.withCurrent,Stack.currentFrame?]) location blockAt normal read pop copied cleanup continuation empty
  exact ⟨updated,returned,size,length,mutable⟩

end
end DuplicatePrefix.S04FinalReturnRuleDriver
