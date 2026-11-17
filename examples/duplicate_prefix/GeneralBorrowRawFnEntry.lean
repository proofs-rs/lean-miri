import duplicate_prefix.GeneralBorrowFnEntryRegistration
import duplicate_prefix.GeneralBorrowConcreteRowReadRange
import duplicate_prefix.GeneralBorrowProtectedChildPositive
import duplicate_prefix.GeneralBorrowConstructorChildActivity
import duplicate_prefix.GeneralBorrowForestFnEntry
namespace DuplicatePrefix.GeneralBorrowRawFnEntry
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
  maximum : Option BorTag
  offset : UInt64
  len : UInt64
  tagged : tree.indexOfTag parentTag = some parent
  positive : DuplicatePrefixBorrowAuthorization.Positive tree global.protectedTags
    (some parent) (some selected) maximum offset len
  distinct : tree.roots.toList.Nodup
  order : ∀ valid : 0 < tree.roots.size, selected ≠ tree.roots[0] → GeneralBorrowWildcardParentTagOrder.ParentTagOrder tree
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
        Nonempty (DuplicatePrefixBorrowAuthorization.Positive output.child.tree output.global.protectedTags
          (some child) (some input.selected) input.maximum input.offset input.len) ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write input.offset (input.offset+input.len) := by
  obtain ⟨allocated,held,frameEq,registeredRuntime,⟨registeredPositive⟩,fresh⟩ :=
    GeneralBorrowFnEntryRegistration.prepare tree global frame allocation input.tagRoom runtime
      input.parent input.selected input.maximum input.offset input.len input.positive
  let registration := GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.1.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowConcreteRowReadRange.access_runtime tree registration.1 registeredRuntime
    input.parentTag input.parent input.selected input.maximum input.tagged (Size.ofBytes input.offset) (Size.ofBytes input.len)
    .VisitChildrenOfAccessed input.offset input.len registeredPositive input.distinct input.order input.short
    (Nat.le_refl _) (Nat.le_refl _)
  obtain ⟨parentNode,parentPresent⟩ := afterPositive.sourcePresent input.parent rfl
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
    GeneralBorrowProtectedChildPositive.construct accessed.tree registration.1 afterRuntime input.parentTag global.nextPointerTag input.parent parentNode
      tagged parentPresent freshAfter room bound heldTag input.selected input.maximum input.offset input.len afterPositive
  have nonzero : input.len ≠ 0 := by intro zero;have p := input.positive.positive;rw [zero] at p;contradiction
  obtain ⟨activityChild,activityLookup,activity⟩ := GeneralBorrowConstructorChildActivity.Protected.construct accessed.tree registration.1 afterRuntime
    input.parentTag global.nextPointerTag input.parent parentNode tagged parentPresent freshAfter room input.offset input.len nonzero afterPositive.bounds
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

/-- Original callback/normal packet API, projected from full Positive initialization. -/
theorem invoke (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
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
        OwnedOn (fun location => GeneralBorrowProtectedCapabilityRange.Child output.child.tree output.global.protectedTags input.parent child location ∧
          Callbacks output.child.tree output.global.protectedTags input.selected input.maximum location)
          input.offset (input.offset+input.len) output.child.tree.locations ∧
        GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree child .Write input.offset (input.offset+input.len) := by
  obtain ⟨output,actual,tag,registered,frameEq,readDone,childDone,afterRuntime,capacity,growth,
    child,lookup,roots,⟨positive⟩,activity⟩ := invoke_positive tree global frame allocation runtime input
  refine ⟨output,actual,tag,registered,frameEq,readDone,childDone,afterRuntime,capacity,growth,
    child,lookup,roots,?_,activity⟩
  intro position valid positiveWindow start stop
  obtain ⟨row⟩ := positive.rows position valid positiveWindow start stop
  exact ⟨row.normal child rfl,row.callbacks⟩
end DuplicatePrefix.GeneralBorrowRawFnEntry
