import duplicate_prefix.GeneralBorrowRawWildcardFnEntryRuntime
import duplicate_prefix.GeneralBorrowWildcardRootConstructorScopedPositive
import duplicate_prefix.GeneralBorrowWildcardRootConstructorActivity
namespace DuplicatePrefix.GeneralBorrowRawWildcardFnEntryScoped
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFnEntryRegistration GeneralBorrowRawWildcardFnEntryRuntime
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Actual fresh allocation, Strong registration, wildcard Read and protected
root construction derive full child Both Positive, internally including every
old callback and fresh selected-root cutoff. No ordering/profile/future data. -/
theorem invoke (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global)
    (offset len : UInt64)
    (positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags none none none offset len)
    (distinct : tree.roots.toList.Nodup) (short : tree.nodes.size < 65536)
    (nodeRoom : tree.nodes.size+1 ≤ 4294967295)
    (tagRoom : global.nextPointerTag.value < 18446744073709551615) :
    ∃ output, operation tree global frame allocation offset len = .ok output ∧
      output.tag = global.nextPointerTag ∧
      output.global = (registered global frame allocation tagRoom).1 ∧
      output.frame.protectedTags = frame.protectedTags.push (allocation,output.tag) ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = tree.locations.size ∧
      output.child.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child,output.child.tree.indexOfTag output.tag = some child ∧
        output.child.tree.roots = tree.roots.push child ∧
        Nonempty (GeneralBorrowFreshRootScopedRow.Positive output.child.tree output.global.protectedTags
          child child output.tag offset len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write offset (offset+len) ∧
        ∃ node,output.child.tree.nodeAt child = some node ∧ node.tag = output.tag ∧ node.parent = none ∧ node.children = #[] ∧ node.isExposed = false := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowWildcardFnEntryRegistration.prepare tree global frame allocation tagRoom runtime none none none offset len positive
  let registration := registered global frame allocation tagRoom
  let accessed := tree.performBorrowAccessRange .wildcard (Size.ofBytes offset) (Size.ofBytes len) .Read
    registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime⟩ := GeneralBorrowSnapshotWildcardRangeRuntime.access tree registration.1 registeredRuntime
    (Size.ofBytes offset) (Size.ofBytes len) .Read .VisitChildrenOfAccessed offset len registeredPositive distinct short
    (Nat.le_refl _) (Nat.le_refl _)
  have freshAfter : GeneralBorrowTagMap.Fresh accessed.tree.tagMapping global.nextPointerTag := by rw [contract.tags];exact fresh
  have room : accessed.tree.nodes.size+1 ≤ 4294967295 := by rw [contract.nodes];exact nodeRoom
  have bound : global.nextPointerTag.value.toNat < registration.1.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag tagRoom
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag tagRoom).value.toNat
    omega
  have heldTag : registration.1.protectedTags.contains global.nextPointerTag = true := by
    unfold ProtectedTags.contains
    rw [held]
    rfl
  have nonzero : len ≠ 0 := by intro zero;have p := positive.positive;rw [zero] at p;contradiction
  have bounds : offset.toNat+len.toNat ≤ accessed.tree.locations.size.bytes.toNat := by
    rw [contract.capacity];exact positive.bounds
  have afterPositive : DuplicatePrefixBorrowAuthorization.Positive accessed.tree registration.1.protectedTags none none none offset len := by
    refine {positive := positive.positive,bounds := bounds,sourcePresent := ?_,wildcardRoot := ?_,rows := contract.rows}
    · intro anchor impossible;cases impossible
    · intro unused
      rw [contract.roots]
      exact positive.wildcardRoot rfl
  have freshBound : GeneralBorrowFreshRootCutoff.Bound accessed.tree global.nextPointerTag := by
    intro index node present
    change accessed.tree.nodes.get index = some node at present
    rw [contract.nodes] at present
    have tagged := runtime.formed.allocator.nodeTags index node present
    have less := GeneralBorrowForestTagHighWater.mapped tree global.protectedTags global.nextPointerTag node.tag
      runtime.below index tagged
    exact UInt64.le_iff_toNat_le.mpr (Nat.le_of_lt less)
  obtain ⟨childDone,childRuntime,capacity,growth,child,lookup,roots,capabilities,geometry⟩ :=
    GeneralBorrowWildcardRootConstructorScopedPositive.construct accessed.tree registration.1 afterRuntime
      global.nextPointerTag freshAfter room bound heldTag freshBound offset len afterPositive
  obtain ⟨activityChild,activityLookup,activity⟩ := GeneralBorrowWildcardRootConstructorActivity.construct accessed.tree registration.1 afterRuntime
    global.nextPointerTag freshAfter room offset len nonzero bounds
  have same : activityChild = child := Option.some.inj (activityLookup.symm.trans lookup)
  subst activityChild
  let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes offset) .wildcard global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
  refine ⟨output,?_,rfl,rfl,frameEq,contract.completed,childDone,childRuntime,capacity.trans contract.capacity,?_,child,lookup,?_,capabilities,activity,geometry⟩
  · simp only [operation,allocated,Except.bind,Except.pure,bind,pure]
    rfl
  · rw [contract.nodes] at growth
    exact growth
  · rw [contract.roots] at roots
    exact roots
end DuplicatePrefix.GeneralBorrowRawWildcardFnEntryScoped
