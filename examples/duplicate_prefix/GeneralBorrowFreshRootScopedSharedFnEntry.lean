import duplicate_prefix.GeneralBorrowRawSharedFnEntry
import duplicate_prefix.GeneralBorrowFreshRootScopedRegistration
import duplicate_prefix.GeneralBorrowFreshRootScopedReadRange
import duplicate_prefix.GeneralBorrowFreshRootScopedSharedPositive
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedSharedFnEntry
open GeneralBorrowRawSharedFnEntry (operation)
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralBorrowSharedCallbacksData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Operation-specific raw FnEntry inputs for a shared helper. The selected
normal component needs Read alone; both other-root callback candidates remain. -/
structure Input (tree : BorrowTree) (global : GlobalState) where
  parentTag : BorTag
  parent : UniIndex
  selected : UniIndex
  maximum : BorTag
  offset : UInt64
  len : UInt64
  tagged : tree.indexOfTag parentTag = some parent
  positive : GeneralBorrowFreshRootScopedReadRow.Positive tree global.protectedTags parent selected maximum offset len
  distinct : tree.roots.toList.Nodup
  short : tree.nodes.size < 65536
  nodeRoom : tree.nodes.size+1 ≤ 4294967295
  tagRoom : global.nextPointerTag.value < 18446744073709551615

/-- Literal shared FnEntry initialization from raw Read-only permission data.
The actual child is active only within the same owner window, derived from
runtime Clean. This is borrowing initialization, not typed MIR execution. -/
theorem invoke (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : Input tree global) :
    ∃ output, operation tree global frame allocation input.parentTag input.offset input.len
        .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧
      output.global = (GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom).1 ∧
      output.global.protectedTags.get output.tag = some .StrongProtector ∧
      output.frame.protectedTags = frame.protectedTags.push (allocation,output.tag) ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = tree.locations.size ∧ output.child.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
        output.child.tree.roots = tree.roots ∧
        Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive output.child.tree output.global.protectedTags
          input.parent input.selected input.maximum input.offset input.len) ∧
        Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive output.child.tree output.global.protectedTags
          child input.selected input.maximum input.offset input.len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Read input.offset (input.offset+input.len) := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFreshRootScopedRegistration.read_prepare tree global frame allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowFreshRootScopedReadRange.access tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.base.sourcePresent
  have tagged : accessed.tree.indexOfTag input.parentTag = some input.parent := by
    unfold BorrowTree.indexOfTag
    rw [contract.tags]
    exact input.tagged
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact input.nodeRoom
  have bound : global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag input.tagRoom
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag input.tagRoom).value.toNat
    omega
  have heldTag : registration.1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  obtain ⟨childDone,childRuntime,capacity,growth,child,lookup,roots,parentPositive,childPositive⟩ :=
    GeneralBorrowFreshRootScopedSharedPositive.shared_read accessed.tree registration.1 afterRuntime input.parentTag global.nextPointerTag input.parent parentNode
      tagged parentPresent freshAfter room bound true heldTag input.selected input.maximum input.offset input.len afterPositive
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.base.positive;rw [zero] at p;contradiction
  obtain ⟨activityChild,activityLookup,activity⟩ := GeneralBorrowConstructorChildActivity.Shared.construct accessed.tree registration.1 afterRuntime
    input.parentTag global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room true input.offset input.len nonzero afterPositive.base.bounds
  have same : activityChild = child := Option.some.inj (activityLookup.symm.trans lookup)
  subst activityChild
  let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen true⟩
  refine ⟨output,?_,rfl,rfl,held,frameEq,contract.completed,childDone,childRuntime,capacity.trans contract.capacity,?_,child,lookup,roots.trans contract.roots,parentPositive,childPositive,activity⟩
  · simp only [operation,allocated,Except.bind,Except.pure,bind,pure]
    rfl
  · rw [contract.nodes] at growth
    exact growth
end DuplicatePrefix.GeneralBorrowFreshRootScopedSharedFnEntry
