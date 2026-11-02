import duplicate_prefix.GeneralBorrowObserverRawSharedFnEntry
import duplicate_prefix.GeneralBorrowObserverSharedLedger
namespace DuplicatePrefix.GeneralBorrowObserverSharedFnEntryVirtual
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowProjection GeneralRangeMapOrigins
open GeneralBorrowObserverReadRange (Observer)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- The exact actual shared FnEntry protocol supplies the mutable observer in
the virtual ledger used by the real helper body/release/restoration proofs.
Every premise refers to BEFORE this call's tag allocation. -/
theorem invoke (tree : BorrowTree) (global : GlobalState) (frame : FrameState) (allocation : AllocId)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : GeneralBorrowRawSharedFnEntry.Input tree global)
    (parentNode observerNode : TreeNode) (observer : UniIndex)
    (parentPresent : tree.nodeAt input.parent = some parentNode) (edge : parentNode.parent = some observer)
    (parentHidden : parentNode.isExposed = false) (parentUnprotected : global.protectedTags.contains parentNode.tag = false)
    (observerPresent : tree.nodeAt observer = some observerNode)
    (observerPath : ((source_normal_projection tree default global.protectedTags).topology.ancestorPath observer.toNat).getLast? = some input.selected.toNat)
    (observerOwned : OwnedOn (Observer tree global.protectedTags observer) input.offset (input.offset+input.len) tree.locations)
    (observerActivity : GeneralBorrowFreshActiveWithin.ActiveWithin tree observer .Write input.offset (input.offset+input.len)) :
    ∃ output, GeneralBorrowRawSharedFnEntry.operation tree global frame allocation input.parentTag input.offset input.len
        .VisitChildrenOfAccessed = .ok output ∧
      output.tag = global.nextPointerTag ∧
      output.global = (GeneralBorrowFnEntryRegistration.registered global frame allocation input.tagRoom).1 ∧
      output.access.status = .Completed ∧ output.child.outcome = .ok () ∧
      DuplicatePrefixBorrowContract.RuntimeFacts output.child.tree output.global ∧
      GeneralBorrowFreshActiveWithin.ActiveWithin output.child.tree observer .Write input.offset (input.offset+input.len) ∧
      ∃ child, output.child.tree.indexOfTag output.tag = some child ∧
        Nonempty (GeneralBorrowReadRowRange.Positive output.child.tree output.global.protectedTags
          child input.selected input.maximum input.offset input.len) ∧
        OwnedOn (Observer output.child.tree (GeneralBorrowObserverReadRow.virtual output.global allocation output.tag parentNode.tag) observer)
          input.offset (input.offset+input.len) output.child.tree.locations := by
  obtain ⟨output,operation,tagEq,accessDone,childDone,finalRuntime,activity,child,lookup,childPositive,observerRows⟩ :=
    GeneralBorrowObserverRawSharedFnEntry.invoke tree global frame allocation runtime input parentNode observerNode observer
      parentPresent edge parentHidden parentUnprotected observerPresent observerPath observerOwned observerActivity
  obtain ⟨standard,standardOperation,_,standardGlobal,_⟩ := GeneralBorrowRawSharedFnEntry.invoke tree global frame allocation runtime input
  have same : standard = output := Except.ok.inj (standardOperation.symm.trans operation)
  subst standard
  have virtualSame : GeneralBorrowObserverReadRow.virtual output.global allocation output.tag parentNode.tag = global.protectedTags := by
    rw [standardGlobal,tagEq]
    exact GeneralBorrowObserverSharedLedger.registered_virtual_runtime tree global runtime frame allocation input.tagRoom
      parentNode.tag parentUnprotected
  refine ⟨output,operation,tagEq,standardGlobal,accessDone,childDone,finalRuntime,activity,child,lookup,childPositive,?_⟩
  rw [virtualSame]
  exact observerRows

end DuplicatePrefix.GeneralBorrowObserverSharedFnEntryVirtual
