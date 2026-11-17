import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAccessData
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedCallFlags
import duplicate_prefix.GeneralBorrowPositiveConcreteWindowAcceptedTargetTag
import duplicate_prefix.GeneralBorrowExposedScopedInactiveWritableAcceptedGraphMetadata
import duplicate_prefix.GeneralBorrowExposedScopedTwoWriteReadRestore
import duplicate_prefix.GeneralBorrowTwoAccessGraphFrame
import duplicate_prefix.GeneralBorrowInactiveWritableCopyGraphRestore
namespace DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedCopyRestore
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
variable {profileMode : ProfileMode}
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option backward.split false
noncomputable section

abbrev ended (call : GeneralBorrowExposedScopedInactiveWritableAsMutToCopy.InputFor profileMode) :=
  (GeneralBorrowExposedScopedInactiveWritableAsMutCallInput.held call.toInput).global.endCall
    (({} : FrameState).addProtector call.id call.tracker.global.nextPointerTag)

def copiedTree (call : GeneralBorrowExposedScopedInactiveWritableAsMutToCopy.InputFor profileMode) : BorrowTree :=
  let read:= (GeneralBorrowExposedScopedInactiveWritableAsMutCallReturn.released call.toInput).performBorrowAccessRange
    (.concrete call.tracker.global.nextPointerTag) (Size.ofBytes call.offset) (Size.ofBytes call.count) .Read (ended call).protectedTags .VisitChildrenOfAccessed
  (read.tree.performBorrowAccessRange (.concrete call.tracker.global.nextPointerTag)
    (Size.ofBytes (call.offset+call.count)) (Size.ofBytes call.count) .Write (ended call).protectedTags .VisitChildrenOfAccessed).tree

/-- Both actual copy accesses change only allocation locations. Snapshot byte
writes are separate memory fields, so the actual returned extra has this same
graph frame when the copy theorem identifies its source extra. -/
theorem graph (call : GeneralBorrowExposedScopedInactiveWritableAsMutToCopy.InputFor profileMode) :
    copiedTree call={GeneralBorrowExposedScopedInactiveWritableAsMutCallReturn.released call.toInput with locations:=(copiedTree call).locations} := by
  unfold copiedTree
  exact GeneralBorrowTwoAccessGraphFrame.frame (GeneralBorrowExposedScopedInactiveWritableAsMutCallReturn.released call.toInput)
    call.tracker.global.nextPointerTag call.offset call.count (ended call).protectedTags

/-- Actual copy post-facts restore BOTH release contracts at the original
wildcard FnEntry target. Node identities/paths come from the actual t4/t5
source constructors, graph transport from both copy accesses, and escaping
protector absence from the original Initial's real insert/endCall history.
No final graph, restored owner, cache, or unheld flag is an Initial premise. -/
theorem restore (s : GeneralBorrowPositiveConcreteWindowAcceptedInput.InitialFor profileMode) (updated : Allocation Provenance BorrowTree)
    (i : GeneralBorrowExposedScopedInactiveWritableLenCallInput.InputFor profileMode) (stage : GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen.InitialFor profileMode)
    (expression : GeneralBorrowExposedScopedInactiveWritableAcceptedExpression.InputFor profileMode) (call : GeneralBorrowExposedScopedInactiveWritableAsMutToCopy.InputFor profileMode)
    (origin : GeneralBorrowPositiveConcreteWindowAcceptedAfterLen.Origin s updated i stage)
    (expressionOrigin : GeneralBorrowExposedScopedInactiveWritableAcceptedAfterLen.Origin stage expression)
    (callOrigin : GeneralBorrowExposedScopedInactiveWritableAcceptedToAsMut.Origin expression call.toInput)
    (context : GeneralBorrowExposedKnownRootRangeData.Context (GeneralBorrowExposedScopedInactiveWritableAsMutCallReturn.released call.toInput)
      (GeneralBorrowFreshMetadataChildMutable.index call.data.input) call.selected call.head call.tail)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedScopedInactiveWritableAccessData.Data (copiedTree call) location (ended call).protectedTags
        (GeneralBorrowFreshMetadataChildMutable.index call.data.input) call.selected call.head call.tail
        (fun position=>call.data.resources.component.support position ∨position=(GeneralBorrowFreshMetadataChildMutable.index call.data.input).toNat)))
      call.offset (call.offset+call.len) (copiedTree call).locations)
     :
    let tree:=copiedTree call
    let target:=expression.data.input.parent
    GeneralBorrowGcAllocator.NodeTags tree ∧ GeneralBorrowGraph.RootsCover tree ∧ tree.nodes.size<65536 ∧ tree.nodes.data.size≤4294967296 ∧
      tree.indexOfTag s.tracker.global.nextPointerTag=some target ∧
      (∃ targetNode,tree.nodeAt target=some targetNode ∧ targetNode.tag=s.tracker.global.nextPointerTag ∧ targetNode.isExposed=false) ∧
      Nonempty (GeneralBorrowExposedKnownRootRangeData.Context tree target call.selected call.head call.tail) ∧
      GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
        (GeneralBorrowExposedScopedInactiveWritableAccessData.Data tree location (ended call).protectedTags target call.selected call.head call.tail
          (fun position=>call.data.resources.component.support position ∨position=(GeneralBorrowFreshMetadataChildMutable.index call.data.input).toNat)))
        s.offset (s.offset+s.len) tree.locations := by
  let target:=expression.data.input.parent
  let expr:=GeneralBorrowFreshMetadataChildDefault.index expression.data.input
  let child:=GeneralBorrowFreshMetadataChildMutable.index call.data.input
  have source:=GeneralBorrowPositiveConcreteWindowAcceptedCallSource.build s updated i stage expression call origin expressionOrigin callOrigin
  have table:=GeneralBorrowPositiveConcreteWindowAcceptedCallFlags.table s updated call source
  have originalTag:=GeneralBorrowPositiveConcreteWindowAcceptedTargetTag.source s updated i stage expression origin expressionOrigin
  have before:=GeneralBorrowExposedScopedInactiveWritableAcceptedGraphMetadata.metadata expression call.toInput callOrigin
  dsimp only at before
  obtain ⟨nodeTags,covered,short,fits,helperLookup,targetNode,exprNode,childNode,targetPresent,targetTag,targetFlag,exprPresent,exprTag,exprHidden,childPresent,childTag,childHidden,paths⟩:=before
  have flags:=GeneralBorrowPositiveConcreteWindowAcceptedUnheld.after_mutable s
  have expressionFree : (ended call).protectedTags.contains exprNode.tag=false := by
    rw [exprTag,←callOrigin.parentTag,source.parentTag,table]
    exact flags.1
  have childFree : (ended call).protectedTags.contains childNode.tag=false := by
    rw [childTag,table,source.tracker]
    exact flags.2
  have restored:=GeneralBorrowInactiveWritableCopyGraphRestore.restore (GeneralBorrowExposedScopedInactiveWritableAsMutCallReturn.released call.toInput) (copiedTree call) (graph call)
    (ended call).protectedTags (fun position=>call.data.resources.component.support position ∨position=child.toNat) child expr target call.selected call.head call.tail s.tracker.global.nextPointerTag nodeTags covered short fits
    targetNode exprNode childNode targetPresent (targetTag.trans originalTag.1) (targetFlag.trans originalTag.2.2) exprPresent exprHidden expressionFree childPresent childHidden childFree
    (fun location=>(paths location (ended call).protectedTags).1) context call.offset (call.offset+call.len) owned call.data.resources.first call.data.resources.rest
  obtain ⟨finalTags,finalCovered,finalShort,finalFits,tagged,hidden,restoredContext,fullOwned⟩:=restored
  let predicate : LocationTree→Prop:=fun location=>Nonempty
    (GeneralBorrowExposedScopedInactiveWritableAccessData.Data (copiedTree call) location (ended call).protectedTags
      target call.selected call.head call.tail (fun position=>call.data.resources.component.support position ∨position=child.toNat))
  change GeneralRangeMapOrigins.OwnedOn predicate call.offset (call.offset+call.len) (copiedTree call).locations at fullOwned
  have shifted : GeneralRangeMapOrigins.OwnedOn predicate s.offset (s.offset+s.len) (copiedTree call).locations := by
    simpa only [source.offset,source.len] using fullOwned
  exact ⟨finalTags,finalCovered,finalShort,finalFits,tagged,hidden,restoredContext,shifted⟩
end
end DuplicatePrefix.GeneralBorrowPositiveConcreteWindowAcceptedCopyRestore
