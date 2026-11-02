import duplicate_prefix.S04FinalReturnInput

namespace DuplicatePrefix.S04FinalReturn
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S04FinalReturnInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section

/-- Composed suffix using the configured pop, physical Bool store and
validation. Pop errors retain their actual state and propagate unchanged.
This helper is not yet identified with the original MIR return rule: return
operand extraction, the copyReturn adapter, cleanup and continuation remain
separate obligations. -/
def operation (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery) (place : MPlaceTy Provenance)
    (value : Bool) (fuel : Nat) : MachineHooks.M MiriMemoryKind Machine.RootUser Unit := fun initial =>
  let inner := PreparedContracts.actualConfig options () remaining span
  let outer := PreparedContracts.actualConfig options () (remaining+1) span
  match (GenericCallReturn.sourceControl inner limits).popFrame () initial with
  | (after,.error error) => .error error after
  | (after,.ok _) => (do
      PlaceMachine.writeMemory outer.access outer.compiler.willValidateMemory (.scalar (Scalar.fromBool value)) place
      ValidityMachine.validateRuntime inner.validity () (fuel+1) ⟨.memory place.mplace,place.layout⟩ true) after

/-- The actual same-allocation pop restores the original destination parent;
the following physical Bool store and Shallow validation use that recovered
capability. Current byte/storage/cache metadata is supplied without a future
Input or whole-machine Resources. Every field transported across the pop is
derived on its literal returned state. This does not construct the preceding
body or claim that its current physical metadata follows from all callers. -/
theorem pop_write
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frames : Array CompilerFrameContext.ActualFrame) (frame : CompilerFrameContext.ActualFrame)
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
    (value : Bool) (fuel : Nat) :
    let released := (destination.entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
    let after := afterPop frames frame machine tracker borrowFrame destination.id destination.entry released
      (thread.topUserRelevantFrame.getD frames.size)
    let outer := PreparedContracts.actualConfig options () (remaining+1) span
    let inner := PreparedContracts.actualConfig options () remaining span
    (GenericCallReturn.sourceControl inner limits).popFrame () (Storage.withCurrent frames frame machine) =
      (after,.ok frame) ∧
    ∃ updated, operation options limits remaining span place value fuel (Storage.withCurrent frames frame machine) =
      .ok () (CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated) ∧
      (do
      PlaceMachine.writeMemory outer.access outer.compiler.willValidateMemory (.scalar (Scalar.fromBool value)) place
      ValidityMachine.validateRuntime inner.validity () (fuel+1) ⟨.memory place.mplace,place.layout⟩ true) after =
      .ok () (CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated) ∧
      updated.byteSize = destination.entry.allocation.byteSize ∧
      updated.len = destination.entry.allocation.len ∧ updated.mutability = .Mut := by
  obtain ⟨pop,afterRuntime,⟨parentPositive⟩⟩ := S04ReturnReleasePop.pop_same_allocation
    options limits remaining span frames frame machine tracker borrowFrame enabled frameTracked
    destination.id destination.entry destination.live zeroTag returnTag zeroIndex child destination.parent selected maximum
    zeroNode returnNode destination.offset zeroTagged zeroPresent zeroHidden quiet returnTagged returnPresent
    returnSame returnEdge returnHidden owned hiddenFrame runtime positive distinct order short activity thread active
  have ownedReturn : (destination.id,returnTag) ∈ borrowFrame.protectedTags.toList := by rw [owned];simp
  obtain ⟨_,_,_,shape,capacity⟩ := S04ReturnReleaseParent.release_to_parent
    destination.entry.allocation.extra tracker.global borrowFrame runtime destination.id returnTag child destination.parent
    selected maximum destination.offset positive returnNode returnPresent returnSame returnEdge returnHidden returnTagged
    ownedReturn hiddenFrame distinct order short activity
  let released := (destination.entry.allocation.extra.releaseProtector returnTag tracker.global.protectedTags).tree
  let next := after_release destination frames frame tracker borrowFrame released
    (thread.topUserRelevantFrame.getD frames.size) shape capacity selected maximum parentPositive
  let after := afterPop frames frame machine tracker borrowFrame destination.id destination.entry released
    (thread.topUserRelevantFrame.getD frames.size)
  have fields := afterPop_fields frames frame machine tracker borrowFrame destination.id destination.entry released
    (thread.topUserRelevantFrame.getD frames.size)
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
  obtain ⟨updated,write,tree,size,length,mutable⟩ := S04FinalReturnValidatedWrite.from_current
    (options := options) (remaining := remaining) span after place next nextRuntime nextDistinct nextOrder nextShort
    destination.tag destination.concrete (by rw [fields.2];exact race)
    (by rw [fields.1];exact backend) (by rw [fields.1];exact ghost) (by rw [fields.1];exact shallow)
    sync nextExtras outside value fuel
  refine ⟨pop,updated,?_,write,size,length,mutable⟩
  have nextId : next.id = destination.id := rfl
  have nextKind : next.entry.kind = destination.entry.kind := rfl
  rw [nextId,nextKind] at write
  simpa only [operation,pop,after,afterPop,released] using write

end
end DuplicatePrefix.S04FinalReturn
