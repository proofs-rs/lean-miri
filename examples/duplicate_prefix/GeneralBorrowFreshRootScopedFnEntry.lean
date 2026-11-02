import duplicate_prefix.GeneralBorrowFreshRootScopedRegistration
import duplicate_prefix.GeneralBorrowFreshRootScopedRange
import duplicate_prefix.GeneralBorrowFreshRootScopedChildPositive
import duplicate_prefix.GeneralBorrowFnEntryRegistration
import duplicate_prefix.GeneralBorrowConcreteRowReadRange
import duplicate_prefix.GeneralBorrowProtectedChildPositive
import duplicate_prefix.GeneralBorrowConstructorChildActivity
import duplicate_prefix.GeneralBorrowForestFnEntry
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedFnEntry
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralBorrowSharedCallbacksData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Raw concrete FnEntry borrowing inputs. Sparse allocator reuse is allowed;
physical MIR/type/cache/return-place validation remains a separate interface. -/
structure Input (tree : BorrowTree) (global : GlobalState) where
  parentTag : BorTag
  parent : UniIndex
  selected : UniIndex
  maximum : BorTag
  offset : UInt64
  len : UInt64
  tagged : tree.indexOfTag parentTag = some parent
  positive : GeneralBorrowFreshRootScopedRow.Positive tree global.protectedTags
    parent selected maximum offset len
  distinct : tree.roots.toList.Nodup
  short : tree.nodes.size < 65536
  nodeRoom : tree.nodes.size+1 ≤ 4294967295
  tagRoom : global.nextPointerTag.value < 18446744073709551615

/-- The actual fresh global tag, Strong frame registration, parent Read and
protected constructor derive runtime and the allocator-chosen child's full
S01 Positive capability and bounded byte activity.
This is the borrowing initialization component, not typed MIR call safety. -/
theorem invoke_positive (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : Input tree global) :
    ∃ output, GeneralBorrowForestFnEntry.operation tree global frame allocation input.parentTag input.offset input.len
        .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧
      output.global = (GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom).1 ∧
      output.frame.protectedTags = frame.protectedTags.push (allocation,output.tag) ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = tree.locations.size ∧ output.child.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
        output.child.tree.roots = tree.roots ∧
        Nonempty (GeneralBorrowFreshRootScopedRow.Positive output.child.tree output.global.protectedTags
          child input.selected input.maximum input.offset input.len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write input.offset (input.offset+input.len) := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFreshRootScopedRegistration.prepare tree global frame allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowFreshRootScopedRange.access_runtime_kind tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .Read .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.base.sourcePresent input.parent rfl
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
  obtain ⟨childDone,childRuntime,capacity,growth,child,lookup,roots,childPositive⟩ :=
    GeneralBorrowFreshRootScopedChildPositive.protected_mutable accessed.tree registration.1 afterRuntime input.parentTag global.nextPointerTag input.parent parentNode
      tagged parentPresent freshAfter room bound heldTag input.selected input.maximum input.offset input.len afterPositive
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.base.positive;rw [zero] at p;contradiction
  obtain ⟨activityChild,activityLookup,activity⟩ := GeneralBorrowConstructorChildActivity.Protected.construct accessed.tree registration.1 afterRuntime
    input.parentTag global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room input.offset input.len nonzero afterPositive.base.bounds
  have same : activityChild = child := Option.some.inj (activityLookup.symm.trans lookup)
  subst activityChild
  let output : GeneralBorrowForestFnEntry.Output := ⟨registration.1,registration.2,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true⟩
  refine ⟨output,?_,rfl,rfl,frameEq,contract.completed,childDone,childRuntime,capacity.trans contract.capacity,?_,child,lookup,roots.trans contract.roots,childPositive,activity⟩
  · simp only [GeneralBorrowForestFnEntry.operation,allocated,Except.bind,Except.pure,bind,pure]
    rfl
  · rw [contract.nodes] at growth
    exact growth


end DuplicatePrefix.GeneralBorrowFreshRootScopedFnEntry
