import duplicate_prefix.GeneralBorrowRawShared
import duplicate_prefix.GeneralBorrowFreshRootScopedSharedFnEntry
import duplicate_prefix.GeneralBorrowReadTagAllocation
import duplicate_prefix.GeneralBorrowFreshRootScopedSharedFnEntry
import duplicate_prefix.GeneralBorrowSharedReadPositive
namespace DuplicatePrefix.GeneralBorrowFreshRootScopedShared
open GeneralBorrowRawShared (Output operation)
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralRangeMapOrigins GeneralBorrowSharedCallbacksData
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000

/-- Raw concrete unprotected shared borrowing inputs. Sparse allocator reuse is allowed;
physical MIR/type/cache/return-place validation remains a separate interface. -/
abbrev Input := GeneralBorrowFreshRootScopedSharedFnEntry.Input

/-- Raw initial Read data derives actual tag allocation/Read/Frozen construction and
full successor Positive at the allocator-chosen child, without registration. -/
theorem invoke_positive (tree : BorrowTree) (global : GlobalState)     (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : Input tree global) :
    ∃ output, operation tree global input.parentTag input.offset input.len
        .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧
      output.global = (GeneralBorrowFnEntryRegistration.advanced global input.tagRoom) ∧
      output.global.protectedTags = global.protectedTags ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      output.child.tree.locations.size = tree.locations.size ∧ output.child.tree.nodes.size ≤ tree.nodes.size+1 ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
        output.child.tree.roots = tree.roots ∧
        Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive output.child.tree output.global.protectedTags
          child input.selected input.maximum input.offset input.len) := by
  obtain ⟨allocated,registeredRuntime,oldPositive,fresh,unheld⟩ :=
    GeneralBorrowReadTagAllocation.prepare tree global input.tagRoom runtime
      input.parent input.selected (some input.maximum) input.offset input.len input.positive.base
  have registeredPositive := input.positive
  let registration := GeneralBorrowFnEntryRegistration.advanced global input.tagRoom
  let accessed := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset)
    (Size.ofBytes input.len) .Read registration.protectedTags .VisitChildrenOfAccessed
  obtain ⟨contract,afterRuntime,⟨afterPositive⟩⟩ := GeneralBorrowFreshRootScopedReadRange.access tree registration registeredRuntime
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
  have bound : global.nextPointerTag.value.toNat < registration.nextPointerTag.value.toNat := by
    have successor := GenericFunctionEntryNumerics.successor_value global.nextPointerTag input.tagRoom
    change global.nextPointerTag.value.toNat < (TypedRetagEmpty.successorTag global.nextPointerTag input.tagRoom).value.toNat
    omega
  have unprotected : registration.protectedTags.contains global.nextPointerTag = false := unheld
  obtain ⟨childDone,childRuntime,capacity,growth,child,lookup,roots,parentPositive,childPositive⟩ :=
    GeneralBorrowFreshRootScopedSharedPositive.shared_read accessed.tree registration afterRuntime input.parentTag global.nextPointerTag input.parent parentNode
      tagged parentPresent freshAfter room bound false (by simpa only [GeneralBorrowFnEntryRegistration.advanced] using unprotected) input.selected input.maximum input.offset input.len afterPositive
  let output : Output := ⟨registration,global.nextPointerTag,accessed,
    accessed.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen false⟩
  refine ⟨output,?_,rfl,rfl,rfl,contract.completed,childDone,childRuntime,capacity.trans contract.capacity,?_,child,lookup,roots.trans contract.roots,childPositive⟩
  · simp only [operation,allocated,Except.bind,Except.pure,bind,pure]
    rfl
  · rw [contract.nodes] at growth
    exact growth

/-- Literal initializer result, suitable for the typed shared Default validator. -/
theorem literal (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : Input tree global) :
    let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
      .Read global.protectedTags .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen false
    read.status = .Completed ∧ child.outcome = .ok () ∧
    DuplicatePrefixBorrowContract.RuntimeFacts child.tree (GeneralBorrowFnEntryRegistration.advanced global input.tagRoom) ∧
    ∃ index, child.tree.indexOfTag global.nextPointerTag = some index ∧
      Nonempty (GeneralBorrowFreshRootScopedReadRow.Positive child.tree global.protectedTags
        index input.selected input.maximum input.offset input.len) := by
  obtain ⟨output,actual,tag,advanced,protections,readDone,childDone,afterRuntime,capacity,growth,index,lookup,roots,positive⟩ :=
    invoke_positive tree global runtime input
  have equation : Except.ok (ε := GlobalStateError) (⟨GeneralBorrowFnEntryRegistration.advanced global input.tagRoom,global.nextPointerTag,
      tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
        .Read global.protectedTags .VisitChildrenOfAccessed,
      (tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
        .Read global.protectedTags .VisitChildrenOfAccessed).tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen false⟩ : Output) = .ok output := by
    simpa only [operation,GeneralBorrowFnEntryRegistration.advanced,TypedRetagEmpty.allocate_tag global input.tagRoom,Except.bind,Except.pure,bind,pure] using actual
  have outputEq := Except.ok.inj equation
  subst output
  exact ⟨readDone,childDone,afterRuntime,index,lookup,positive⟩

end DuplicatePrefix.GeneralBorrowFreshRootScopedShared
