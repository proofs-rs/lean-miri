import duplicate_prefix.S04ActiveSameReturnPop
import duplicate_prefix.S03FinalReturnRuleCopyBounds
import duplicate_prefix.S03FinalReturnInputBounds
import duplicate_prefix.S04FinalReturnVariantsDriver

namespace DuplicatePrefix.S03ActiveSameReturnDriverBounds
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S03FinalReturnInputBounds S04FinalReturnVariantsInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Actual same-allocation Return body after transporting the return child's
activity across the source release. The copy, validation, cleanup and stop
execute from derived release and parent-authorization facts. -/
theorem return_effect
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame)
    (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (place : MPlaceTy Provenance) (destination : Destination machine place)
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
    (returnTag : BorTag) (child selected : UniIndex) (maximum : Option BorTag)
    (returnNode : TreeNode)
    (returnTagged : destination.entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : destination.entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (returnEdge : returnNode.parent = some destination.parent)
    (returnHidden : returnNode.isExposed = false)
    (owned : borrowFrame.protectedTags = #[(destination.id,sourceTag),(destination.id,returnTag)])
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
    (varargs : frame.vaList = #[]) :
    let sourceReleased := (destination.entry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree
    let priorMemory := StackPopRelease.commitTree machine.memory destination.id destination.entry sourceReleased
    let released := (sourceReleased.releaseProtector returnTag tracker.global.protectedTags).tree
    let after := S04FinalReturnVariantsInput.afterPop #[] frame machine tracker borrowFrame priorMemory
      destination.id destination.entry released (thread.topUserRelevantFrame.getD 0)
    ∃ updated, ControlFlow.returnFromCurrentFrame
      (GenericCallReturn.sourceControl (PreparedContracts.actualConfig options () (remaining+1) span) limits) () false
      (Storage.withCurrent #[] frame machine) =
      (CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated,.ok ()) ∧
      updated.byteSize = destination.entry.allocation.byteSize ∧
      updated.len = destination.entry.allocation.len ∧ updated.mutability = .Mut := by
  obtain ⟨pop,afterRuntime,⟨parentPositive⟩⟩ := S04ActiveSameReturnPop.pop_after_source_activity
    options limits (remaining+1) span #[] frame machine tracker borrowFrame enabled frameTracked
    destination.id destination.entry destination.live
    sourceTag returnTag sourceChild sourceSelected child destination.parent selected sourceMaximum maximum
    sourceOffset sourceLen destination.offset sourceNode returnNode sourceTagged sourcePresent sourceHidden
    sourceRuntime sourcePositive sourceDistinct sourceOrder sourceShort sourceActivity
    returnTagged returnPresent returnSame returnEdge returnHidden owned hiddenFrame
    positive distinct order short disjoint activity thread active
  let sourceReleased := (destination.entry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree
  let priorMemory := StackPopRelease.commitTree machine.memory destination.id destination.entry sourceReleased
  let released := (sourceReleased.releaseProtector returnTag tracker.global.protectedTags).tree
  have sourceShape := GeneralBorrowStructuralReleaseGeometryFrame.release destination.entry.allocation.extra tracker.global.protectedTags sourceTag
  have returnShape := GeneralBorrowStructuralReleaseGeometryFrame.release sourceReleased tracker.global.protectedTags returnTag
  have shape : released = {destination.entry.allocation.extra with locations := released.locations} := by
    calc
      released = {sourceReleased with locations := released.locations} := returnShape
      _ = _ := by
        change sourceReleased = {destination.entry.allocation.extra with locations := sourceReleased.locations} at sourceShape
        rw [sourceShape]
  have sourceGeometry := GeneralBorrowStructuralReleaseGeometry.release destination.entry.allocation.extra tracker.global.protectedTags sourceTag runtime.formed.well
  have returnGeometry := GeneralBorrowStructuralReleaseGeometry.release sourceReleased tracker.global.protectedTags returnTag sourceGeometry.1
  have capacity : released.locations.size = destination.entry.allocation.extra.locations.size := returnGeometry.2.trans sourceGeometry.2
  let next := S03FinalReturnInputBounds.after_release destination #[] frame tracker borrowFrame priorMemory released
    (thread.topUserRelevantFrame.getD 0) shape capacity selected maximum parentPositive
  let after := S04FinalReturnVariantsInput.afterPop #[] frame machine tracker borrowFrame priorMemory
    destination.id destination.entry released (thread.topUserRelevantFrame.getD 0)
  have fields := S04FinalReturnVariantsInput.afterPop_fields #[] frame machine tracker borrowFrame priorMemory
    destination.id destination.entry released (thread.topUserRelevantFrame.getD 0)
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
  have nextExtras : after.machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == next.id) = some (next.id,⟨none,sync⟩) := by
    change after.machine.user.payload.payload.user.runtime.extras.allocations.find?
      (fun row => row.1 == destination.id) = _
    rw [fields.1]
    exact extras
  obtain ⟨updated,copied,size,length,mutable⟩ := S03FinalReturnRuleCopyBounds.from_current
    (options := options) limits (remaining := remaining) span after place next nextRuntime nextDistinct nextOrder nextShort
    destination.tag destination.concrete (by rw [fields.2];exact race)
    (by rw [fields.1];exact backend) (by rw [fields.1];exact ghost) (by rw [fields.1];exact shallow)
    sync nextExtras outside value fuel debugOff validationFuel frame.returnPlace returnPlace
  refine ⟨updated,?_,size,length,mutable⟩
  exact S04FinalReturnVariantsDriver.finish options limits remaining span frame machine after
    (CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated) value ghost
    sourceBody location valid0 live0 cached0 noLocalClocks continuation immediateLocals varargs pop copied rfl

end
end DuplicatePrefix.S03ActiveSameReturnDriverBounds

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S03ActiveSameReturnDriverBounds.return_effect) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved active same return driver dependency {dependency}"
