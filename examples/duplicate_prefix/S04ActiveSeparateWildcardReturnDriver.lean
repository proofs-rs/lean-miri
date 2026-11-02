import duplicate_prefix.S04ActiveSeparateWildcardReturnPop
import duplicate_prefix.S04FinalReturnWildcardInput
import duplicate_prefix.S04FinalReturnWildcardCopy
import duplicate_prefix.S04FinalReturnVariantsDriver

namespace DuplicatePrefix.S04ActiveSeparateWildcardReturnDriver
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S04FinalReturnVariantsInput S04FinalReturnWildcardInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Original source Return driver at the fixed duplicate_prefix return block:
actual local read, current-state wildcard destination and argument protector dispatch, physical
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
    (returnTag : BorTag) (child : UniIndex)
    (returnNode : TreeNode)
    (returnTagged : destination.entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : destination.entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (parentless : returnNode.parent = none)
    (leaf : returnNode.children = #[])
    (returnHidden : returnNode.isExposed = false)
    (owned : borrowFrame.protectedTags = #[(sourceId,sourceTag),(destination.id,returnTag)])
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
    (varargs : frame.vaList = #[]) :
    let released := (destination.entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
    let after := S04FinalReturnVariantsInput.afterPop #[] frame machine tracker borrowFrame (StackPopRelease.commitTree machine.memory sourceId sourceEntry (sourceEntry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree) destination.id destination.entry released
      (thread.topUserRelevantFrame.getD 0)
    ∃ updated, ControlFlow.returnFromCurrentFrame
      (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () (remaining+1) span) limits) () false
      (Storage.withCurrent #[] frame machine) =
      (CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated,.ok ()) ∧
      updated.byteSize = destination.entry.allocation.byteSize ∧
      updated.len = destination.entry.allocation.len ∧ updated.mutability = .Mut := by
  obtain ⟨pop,afterRuntime,⟨wildcardPositive⟩⟩ := S04ActiveSeparateWildcardReturnPop.pop_active_separate
    options limits (remaining+1) span #[] frame machine tracker borrowFrame enabled frameTracked
    sourceId destination.id separate sourceEntry destination.entry sourceLive destination.live
    sourceTag returnTag sourceChild sourceSelected child sourceMaximum sourceOffset sourceLen destination.offset sourceNode returnNode
    sourceTagged sourcePresent sourceHidden sourceRuntime sourcePositive sourceDistinct sourceOrder sourceShort sourceActivity
    returnTagged returnPresent returnSame parentless leaf returnHidden owned hiddenFrame runtime positive distinct order exposed notPrimary short activity thread active
  have ownedReturn : (destination.id,returnTag) ∈ borrowFrame.protectedTags.toList := by rw [owned];simp
  obtain ⟨_,_,_,shape,capacity⟩ := S04ReturnWildcardOrderedRestore.release_to_wildcard
    destination.entry.allocation.extra tracker.global borrowFrame runtime order destination.id returnTag child destination.offset 1
    exposed positive returnNode returnPresent returnSame parentless leaf returnHidden returnTagged ownedReturn
    hiddenFrame notPrimary distinct short activity
  let released := (destination.entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
  let next := S04FinalReturnWildcardInput.after_release destination #[] frame tracker borrowFrame (StackPopRelease.commitTree machine.memory sourceId sourceEntry (sourceEntry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree) released
    (thread.topUserRelevantFrame.getD 0) capacity wildcardPositive
  let after := S04FinalReturnVariantsInput.afterPop #[] frame machine tracker borrowFrame (StackPopRelease.commitTree machine.memory sourceId sourceEntry (sourceEntry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree) destination.id destination.entry released
    (thread.topUserRelevantFrame.getD 0)
  have fields := S04FinalReturnVariantsInput.afterPop_fields #[] frame machine tracker borrowFrame (StackPopRelease.commitTree machine.memory sourceId sourceEntry (sourceEntry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree) destination.id destination.entry released
    (thread.topUserRelevantFrame.getD 0)
  have nextRuntime : DuplicatePrefixBorrowContract.RuntimeFacts next.entry.allocation.extra next.tracker.global := afterRuntime
  have nextDistinct : next.entry.allocation.extra.roots.toList.Nodup := by
    change released.roots.toList.Nodup
    rw [congrArg BorrowTree.roots shape]
    exact distinct
  have nextShort : next.entry.allocation.extra.nodes.size < 65536 := by
    change released.nodes.size < 65536
    rw [congrArg BorrowTree.nodes shape]
    exact short
  have nextExtras : after.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == next.id) =
      some (next.id,⟨none,sync⟩) := by
    change after.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = _
    rw [fields.1]
    exact extras
  obtain ⟨updated,copied,size,length,mutable⟩ := S04FinalReturnWildcardCopy.from_current
    (options := options) limits (remaining := remaining) span after place next nextRuntime nextDistinct nextShort
    destination.wildcard (by rw [fields.2];exact race)
    (by rw [fields.1];exact backend) (by rw [fields.1];exact ghost) (by rw [fields.1];exact shallow)
    sync nextExtras outside value fuel debugOff validationFuel frame.returnPlace returnPlace
  refine ⟨updated,?_,size,length,mutable⟩
  exact S04FinalReturnVariantsDriver.finish options limits remaining span frame machine after
    (CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated) value ghost
    sourceBody location valid0 live0 cached0 noLocalClocks continuation immediateLocals varargs pop copied rfl

end
end DuplicatePrefix.S04ActiveSeparateWildcardReturnDriver
