import duplicate_prefix.S04ActiveSameReturnPop
import duplicate_prefix.S04ActiveSeparateWildcardReturnStep
namespace DuplicatePrefix.S02WildcardReturnSameStep
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open S04FinalReturnVariantsInput S04FinalReturnWildcardInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
noncomputable section
/-- Actual Return for an active source and parentless wildcard return child on
one allocation. The source may itself be a parentless FnEntry root. All release,
physical write and validation success is derived from current point data. -/
theorem step
    (options : EvalConfigurationCore.Options) (limits : ExecutionMachine.Limits)
    (remaining : Nat) (span : PreparedContracts.FixedSpanQuery)
    (frame : CompilerFrameContext.ActualFrame) (machine : MachineHooks.MachineState MiriMemoryKind Machine.RootUser)
    (tracker : MachineHooks.BorrowState) (borrowFrame : FrameState)
    (enabled : machine.borrowTracker = some tracker) (frameTracked : frame.extra.borrowTracker = some borrowFrame)
    (place : MPlaceTy Provenance) (destination : Destination machine place)
    (sourceTag : BorTag) (sourceChild sourceSelected : UniIndex) (sourceMaximum : Option BorTag)
    (sourceOffset sourceLen : UInt64) (sourceNode : TreeNode)
    (sourceTagged : destination.entry.allocation.extra.indexOfTag sourceTag = some sourceChild)
    (sourcePresent : destination.entry.allocation.extra.nodeAt sourceChild = some sourceNode)
    (sourceHidden : sourceNode.isExposed = false)
    (sourcePositive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra tracker.global.protectedTags
      (some sourceChild) (some sourceSelected) sourceMaximum sourceOffset sourceLen)
    (sourceActivity : GeneralBorrowFreshActiveWithin.ActiveWithin destination.entry.allocation.extra sourceChild .Write sourceOffset (sourceOffset+sourceLen))
    (returnTag : BorTag) (child : UniIndex) (returnNode : TreeNode)
    (returnTagged : destination.entry.allocation.extra.indexOfTag returnTag = some child)
    (returnPresent : destination.entry.allocation.extra.nodeAt child = some returnNode)
    (returnSame : returnNode.tag = returnTag) (parentless : returnNode.parent = none) (leaf : returnNode.children = #[])
    (returnHidden : returnNode.isExposed = false)
    (owned : borrowFrame.protectedTags = #[(destination.id,sourceTag),(destination.id,returnTag)])
    (hiddenFrame : S04ReturnReleaseParent.HiddenFrame destination.entry.allocation.extra borrowFrame)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts destination.entry.allocation.extra tracker.global)
    (positive : DuplicatePrefixBorrowAuthorization.Positive destination.entry.allocation.extra tracker.global.protectedTags
      (some child) (some child) (some returnTag) destination.offset 1)
    (distinct : destination.entry.allocation.extra.roots.toList.Nodup)
    (order : GeneralBorrowWildcardParentTagOrder.ParentTagOrder destination.entry.allocation.extra)
    (exposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound destination.entry.allocation.extra returnTag)
    (notPrimary : ∀ valid : 0 < destination.entry.allocation.extra.roots.size, destination.entry.allocation.extra.roots[0] ≠ child)
    (short : destination.entry.allocation.extra.nodes.size < 65536)
    (disjoint : (sourceOffset+sourceLen).toNat ≤ destination.offset.toNat ∨ (destination.offset+1).toNat ≤ sourceOffset.toNat)
    (activity : GeneralBorrowFreshActiveWithin.ActiveWithin
      (destination.entry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree child .Write destination.offset (destination.offset+1))
    (thread : Miri.Concurrency.ThreadRecord) (active : machine.threads.activeThread? = some thread)
    (race : machine.dataRace = none) (backend : machine.user.payload.payload.user.backend = .none)
    (ghost : machine.user.payload.ghost = false) (shallow : machine.user.payload.validation = .Shallow)
    (sync : Array (Size × MemoryExtras.Entry Unit))
    (extras : machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = some (destination.id,⟨none,sync⟩))
    (outside : ∀ row ∈ sync, row.1.bytes.toNat < destination.offset.toNat ∨ destination.offset.toNat+1 ≤ row.1.bytes.toNat)
    (value : Bool) (fuel : Nat) (debugOff : options.place.debugAssertions = false)
    (validationFuel : options.limits.validation = fuel+1)
    (sourceBody : frame.body = RootBody.reflected.body.body) (location : frame.location = .mir ⟨10,0⟩)
    (valid0 : (0 : MIR.LocalId) < frame.locals.size)
    (live0 : frame.locals[0].value = .live (.immediate (.scalar (.fromBool value))))
    (cached0 : frame.locals[0].layout = some RootCompilerFacts.boolLayout) (noLocalClocks : frame.extra.dataRace = none)
    (returnPlace : frame.returnPlace.toRuntimePlace = ⟨.memory place.mplace,place.layout⟩)
    (continuation : frame.returnContinuation = .stop true)
    (immediateLocals : ∀ slot ∈ frame.locals, ∀ memory, slot.value ≠ .live (.indirect memory)) (varargs : frame.vaList = #[])
    (unchecked : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).checkedArithmetic = false)
    (noGc : ((PreparedContracts.actualConfig options () (remaining+1) span).terminators.getControl machine.user).gcInterval = 0)
    (fixed : machine.threads.fixedScheduling = true) :
    let accounted := S04FinalReturnRuleAccounting.machine options remaining span frame machine
    let sourceReleased := (destination.entry.allocation.extra.releaseProtector sourceTag tracker.global.protectedTags).tree
    let priorMemory := StackPopRelease.commitTree accounted.memory destination.id destination.entry sourceReleased
    let released := (sourceReleased.releaseProtector returnTag tracker.global.protectedTags).tree
    let after := S04FinalReturnVariantsInput.afterPop #[] frame accounted tracker borrowFrame priorMemory destination.id destination.entry released (thread.topUserRelevantFrame.getD 0)
    ∃ updated, ExecutionMachine.step (PreparedContracts.actualConfig options () (remaining+1) span) limits () (Storage.withCurrent #[] frame machine) =
      (CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated,.ok true) ∧
      updated.byteSize = destination.entry.allocation.byteSize ∧ updated.len = destination.entry.allocation.len ∧ updated.mutability = .Mut := by
  let cfg := PreparedContracts.actualConfig options () (remaining+1) span
  let initial := Storage.withCurrent #[] frame machine
  let accounted := S04FinalReturnRuleAccounting.machine options remaining span frame machine
  let current := Storage.withCurrent #[] frame accounted
  let dest := S04FinalReturnWildcard.accounted_destination options remaining span frame machine place destination
  have metadata := S04FinalReturnRuleAccounting.metadata options remaining span frame machine
  let tree := destination.entry.allocation.extra
  let sourceReleased := (tree.releaseProtector sourceTag tracker.global.protectedTags).tree
  obtain ⟨sourceDone,_,_,_,sourceShape,sourceCapacity⟩ := GeneralBorrowBothProtectorRelease.release tree tracker.global runtime
    sourceTag sourceChild sourceSelected sourceMaximum sourceOffset sourceLen sourcePositive sourceNode sourcePresent sourceHidden sourceTagged distinct (fun _ _ => order) short sourceActivity
  obtain ⟨_,sourceRuntime,⟨sourcePositiveAfter⟩⟩ := S02DisjointReleaseAuthorization.positive tree tracker.global runtime
    sourceTag sourceChild sourceSelected sourceMaximum sourceOffset sourceLen sourcePositive sourceNode sourcePresent sourceHidden sourceTagged distinct (fun _ _ => order) short sourceActivity
    (some child) (some child) (some returnTag) destination.offset 1 positive disjoint
  have nodes := congrArg BorrowTree.nodes sourceShape
  have roots := congrArg BorrowTree.roots sourceShape
  have tags := congrArg BorrowTree.tagMapping sourceShape
  change sourceReleased.nodes = tree.nodes at nodes
  change sourceReleased.roots = tree.roots at roots
  change sourceReleased.tagMapping = tree.tagMapping at tags
  have nextPresent : sourceReleased.nodeAt child = some returnNode := by change sourceReleased.nodes.get child = _;rw [nodes];exact returnPresent
  have nextTagged : sourceReleased.indexOfTag returnTag = some child := by unfold BorrowTree.indexOfTag;change sourceReleased.tagMapping.get returnTag = _;rw [tags];exact returnTagged
  have nextHidden : S04ReturnReleaseParent.HiddenFrame sourceReleased borrowFrame := by
    intro row member index node present same
    apply hiddenFrame row member index node _ same
    change sourceReleased.nodes.get index = some node at present
    change tree.nodes.get index = some node
    rwa [nodes] at present
  have nextOrder : GeneralBorrowWildcardParentTagOrder.ParentTagOrder sourceReleased := by
    simpa only [GeneralBorrowWildcardParentTagOrder.ParentTagOrder,nodes] using order
  have nextExposed : GeneralBorrowFreshRootSupportCutoff.ExposedBound sourceReleased returnTag := by
    intro index node present exposedNode
    apply exposed index node _ exposedNode
    change sourceReleased.nodes.get index = some node at present
    change tree.nodes.get index = some node
    rwa [nodes] at present
  have nextNotPrimary : ∀ valid : 0 < sourceReleased.roots.size, sourceReleased.roots[0] ≠ child := by
    intro valid
    simpa only [roots] using notPrimary (by simpa only [roots] using valid)
  have ownedReturn : (destination.id,returnTag) ∈ borrowFrame.protectedTags.toList := by rw [owned];simp
  obtain ⟨returnDone,afterRuntime,⟨wildcardPositive⟩,returnShape,returnCapacity⟩ := S04ReturnWildcardOrderedRestore.release_to_wildcard
    sourceReleased tracker.global borrowFrame sourceRuntime nextOrder destination.id returnTag child destination.offset 1 nextExposed
    sourcePositiveAfter returnNode nextPresent returnSame parentless leaf returnHidden nextTagged ownedReturn nextHidden nextNotPrimary
    (by rw [roots];exact distinct) (by rw [nodes];exact short) activity
  let released := (sourceReleased.releaseProtector returnTag tracker.global.protectedTags).tree
  have sourceRelease : tree.releaseProtector sourceTag tracker.global.protectedTags = ⟨sourceReleased,.Released⟩ := by
    cases h : tree.releaseProtector sourceTag tracker.global.protectedTags with
    | mk result status => simp only [h] at sourceDone;cases sourceDone;simp only [sourceReleased,h]
  have returnRelease : sourceReleased.releaseProtector returnTag tracker.global.protectedTags = ⟨released,.Released⟩ := by
    cases h : sourceReleased.releaseProtector returnTag tracker.global.protectedTags with
    | mk result status => simp only [h] at returnDone;cases returnDone;simp only [released,h]
  let priorMemory := StackPopRelease.commitTree accounted.memory destination.id destination.entry sourceReleased
  have nextLive := StackPopRelease.lookup_commit_same accounted.memory destination.id destination.entry sourceReleased
  have plan : StackPopRelease.Plan tracker.global.protectedTags borrowFrame.protectedTags.toList accounted.memory
      (StackPopRelease.commitTree priorMemory destination.id destination.entry released) := by
    rw [owned]
    exact .live destination.id sourceTag destination.entry sourceReleased [(destination.id,returnTag)] accounted.memory _
      destination.live sourceRelease (.live destination.id returnTag {destination.entry with allocation := destination.entry.allocation.setExtra sourceReleased}
        released [] _ _ nextLive returnRelease (.nil _))
  let after := S04FinalReturnVariantsInput.afterPop #[] frame accounted tracker borrowFrame priorMemory destination.id destination.entry released (thread.topUserRelevantFrame.getD 0)
  have pop := ActualPopPlan.pop_of_plan options limits (remaining+1) span #[] frame accounted tracker borrowFrame enabled frameTracked _ plan thread active
  have capacity : released.locations.size = tree.locations.size := returnCapacity.trans sourceCapacity
  let next := S04FinalReturnWildcardInput.after_release dest #[] frame tracker borrowFrame priorMemory released (thread.topUserRelevantFrame.getD 0) capacity wildcardPositive
  have fields := S04FinalReturnVariantsInput.afterPop_fields #[] frame accounted tracker borrowFrame priorMemory destination.id destination.entry released (thread.topUserRelevantFrame.getD 0)
  have finalShape : released = {tree with locations := released.locations} := by
    calc
      released = {sourceReleased with locations := released.locations} := returnShape
      _ = _ := by
        change sourceReleased = {tree with locations := sourceReleased.locations} at sourceShape
        rw [sourceShape]
  have nextDistinct : next.entry.allocation.extra.roots.toList.Nodup := by change released.roots.toList.Nodup;rw [congrArg BorrowTree.roots finalShape];exact distinct
  have nextShort : next.entry.allocation.extra.nodes.size < 65536 := by change released.nodes.size < 65536;rw [congrArg BorrowTree.nodes finalShape];exact short
  have nextExtras : after.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == next.id) = some (next.id,⟨none,sync⟩) := by
    change after.machine.user.payload.payload.user.runtime.extras.allocations.find? (fun row => row.1 == destination.id) = some (destination.id,⟨none,sync⟩)
    rw [fields.1,metadata.2.2.2.2];exact extras
  obtain ⟨updated,copied,size,length,mutable⟩ := S04FinalReturnWildcardCopy.from_current (options := options) limits (remaining := remaining) span after place next
    afterRuntime nextDistinct nextShort destination.wildcard (by rw [fields.2];exact race)
    (by rw [fields.1,metadata.2.2.2.1];exact backend) (by rw [fields.1,metadata.2.1];exact ghost)
    (by rw [fields.1,metadata.2.2.1];exact shallow) sync nextExtras outside value fuel debugOff validationFuel frame.returnPlace returnPlace
  have returned := S04FinalReturnVariantsDriver.finish options limits remaining span frame accounted after
    (CanonicalCopy.replaceAllocation after destination.id destination.entry.kind updated) value (by rw [metadata.2.1];exact ghost)
    sourceBody location valid0 live0 cached0 noLocalClocks continuation immediateLocals varargs pop copied rfl
  have accounting := SourceControl.before_terminator cfg limits () initial (CanonicalConfigFacts.actual_term_get_set options () (remaining+1) span)
    (CanonicalConfigFacts.actual_term_set_set options () (remaining+1) span) unchecked noGc fixed
  let block := RootBody.reflected.body.body.basicBlocks[10]'(by with_unfolding_all decide +kernel)
  have blockAt : frame.body.basicBlocks[10]? = some block := by rw [sourceBody];simp [block]
  have noStatement : block.statements[0]? = none := by with_unfolding_all rfl
  have kind : block.terminator.kind = .Return := by with_unfolding_all rfl
  refine ⟨updated,?_,size,length,mutable⟩
  exact GenericCallReturn.return_step_exact cfg limits () initial current _ frame ⟨10,0⟩ block
    (by simp [initial,Storage.withCurrent,Stack.currentFrame?]) location blockAt noStatement kind accounting returned
end
end DuplicatePrefix.S02WildcardReturnSameStep
open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02WildcardReturnSameStep.step) do
    unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
      throwError "unapproved same wildcard Return step dependency {dependency}"
