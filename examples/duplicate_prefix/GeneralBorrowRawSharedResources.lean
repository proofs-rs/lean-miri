import duplicate_prefix.GeneralBorrowRawSharedExpression
namespace DuplicatePrefix.GeneralBorrowRawSharedResources
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowRawShared
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 3000000
/-- Literal initializer result, suitable for the typed shared Default validator. -/
theorem resources (tree : BorrowTree) (global : GlobalState)
    (runtime : DuplicatePrefixBorrowContract.RuntimeFacts tree global) (input : Input tree global) :
    let read := tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
      .Read global.protectedTags .VisitChildrenOfAccessed
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen false
    read.status = .Completed ∧ child.outcome = .ok () ∧
    child.tree.locations.size = tree.locations.size ∧ child.tree.nodes.size ≤ tree.nodes.size+1 ∧
    child.tree.roots = tree.roots ∧
    DuplicatePrefixBorrowContract.RuntimeFacts child.tree (GeneralBorrowFnEntryRegistration.advanced global input.tagRoom) ∧
    ∃ index, child.tree.indexOfTag global.nextPointerTag = some index ∧
      Nonempty (GeneralBorrowReadRowRange.Positive child.tree global.protectedTags
        index input.selected input.maximum input.offset input.len) := by
  obtain ⟨output,actual,tag,advanced,protections,readDone,childDone,afterRuntime,capacity,growth,index,lookup,roots,positive⟩ :=
    GeneralBorrowRawShared.invoke_positive tree global runtime input
  have equation : Except.ok (ε := GlobalStateError) (⟨GeneralBorrowFnEntryRegistration.advanced global input.tagRoom,global.nextPointerTag,
      tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
        .Read global.protectedTags .VisitChildrenOfAccessed,
      (tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
        .Read global.protectedTags .VisitChildrenOfAccessed).tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) global.nextPointerTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshAnchor.sharedState) .Frozen false⟩ : Output) = .ok output := by
    simpa only [GeneralBorrowRawShared.operation,GeneralBorrowFnEntryRegistration.advanced,TypedRetagEmpty.allocate_tag global input.tagRoom,Except.bind,Except.pure,bind,pure] using actual
  have outputEq := Except.ok.inj equation
  subst output
  exact ⟨readDone,childDone,capacity,growth,roots,afterRuntime,index,lookup,positive⟩

end DuplicatePrefix.GeneralBorrowRawSharedResources
