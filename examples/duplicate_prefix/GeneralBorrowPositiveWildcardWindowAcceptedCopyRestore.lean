import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedCallFlags
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowAcceptedTargetTag
import duplicate_prefix.GeneralBorrowExposedScopedWindowWritableAcceptedGraphMetadata
import duplicate_prefix.GeneralBorrowExposedScopedTwoWriteReadRestore
import duplicate_prefix.GeneralBorrowTwoAccessGraphFrame
import duplicate_prefix.GeneralBorrowCopyGraphRestore
namespace DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedCopyRestore
open Miri Miri.Input Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree Miri.Interpreter
open GeneralBorrowProjection
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
set_option backward.split false
noncomputable section

abbrev ended (call : GeneralBorrowExposedScopedWindowWritableAsMutToCopy.Input) :=
  (GeneralBorrowExposedScopedWindowWritableAsMutCallInput.held call.toInput).global.endCall
    (({} : FrameState).addProtector call.id call.tracker.global.nextPointerTag)

def copiedTree (call : GeneralBorrowExposedScopedWindowWritableAsMutToCopy.Input) : BorrowTree :=
  let read:= (GeneralBorrowExposedScopedWindowWritableAsMutCallReturn.released call.toInput).performBorrowAccessRange
    (.concrete call.tracker.global.nextPointerTag) (Size.ofBytes call.offset) (Size.ofBytes call.count) .Read (ended call).protectedTags .VisitChildrenOfAccessed
  (read.tree.performBorrowAccessRange (.concrete call.tracker.global.nextPointerTag)
    (Size.ofBytes (call.offset+call.count)) (Size.ofBytes call.count) .Write (ended call).protectedTags .VisitChildrenOfAccessed).tree

/-- Both actual copy accesses change only allocation locations. Snapshot byte
writes are separate memory fields, so the actual returned extra has this same
graph frame when the copy theorem identifies its source extra. -/
theorem graph (call : GeneralBorrowExposedScopedWindowWritableAsMutToCopy.Input) :
    copiedTree call={GeneralBorrowExposedScopedWindowWritableAsMutCallReturn.released call.toInput with locations:=(copiedTree call).locations} := by
  unfold copiedTree
  exact GeneralBorrowTwoAccessGraphFrame.frame (GeneralBorrowExposedScopedWindowWritableAsMutCallReturn.released call.toInput)
    call.tracker.global.nextPointerTag call.offset call.count (ended call).protectedTags

/-- Actual copy post-facts restore BOTH release contracts at the original
wildcard FnEntry target. Node identities/paths come from the actual t4/t5
source constructors, graph transport from both copy accesses, and escaping
protector absence from the original Initial's real insert/endCall history.
No final graph, restored owner, cache, or unheld flag is an Initial premise. -/
theorem restore (s : GeneralBorrowPositiveWildcardWindowAcceptedInput.Initial) (updated : Allocation Provenance BorrowTree)
    (i : GeneralBorrowExposedScopedWindowWritableLenCallInput.Input) (stage : GeneralBorrowExposedScopedWindowWritableAcceptedAfterLen.Initial)
    (expression : GeneralBorrowExposedScopedWindowWritableAcceptedExpression.Input) (call : GeneralBorrowExposedScopedWindowWritableAsMutToCopy.Input)
    (origin : GeneralBorrowPositiveWildcardWindowAcceptedAfterLen.Origin s updated i stage)
    (expressionOrigin : GeneralBorrowExposedScopedWindowWritableAcceptedAfterLen.Origin stage expression)
    (callOrigin : GeneralBorrowExposedScopedWindowWritableAcceptedToAsMut.Origin expression call.toInput)
    (context : GeneralBorrowExposedKnownRootRangeData.Context (GeneralBorrowExposedScopedWindowWritableAsMutCallReturn.released call.toInput)
      (GeneralBorrowFreshMetadataChildMutable.index call.data.input) call.selected call.head call.tail)
    (owned : GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
      (GeneralBorrowExposedScopedLeafWriteReadClosed.Data (copiedTree call) location (ended call).protectedTags
        (GeneralBorrowFreshMetadataChildMutable.index call.data.input) call.selected call.head call.tail))
      call.offset (call.offset+call.len) (copiedTree call).locations)
    (sourceInitialized : InitMaskCopy.InitializedOn s.entry.allocation.initializationMask
      (Size.ofBytes s.offset) (Size.ofBytes (s.offset+s.count))) :
    let tree:=copiedTree call
    let target:=expression.data.input.parent
    GeneralBorrowGcAllocator.NodeTags tree ∧ GeneralBorrowGraph.RootsCover tree ∧ tree.nodes.size<65536 ∧ tree.nodes.data.size≤4294967296 ∧
      tree.indexOfTag s.tracker.global.nextPointerTag=some target ∧
      (∃ targetNode,tree.nodeAt target=some targetNode ∧ targetNode.tag=s.tracker.global.nextPointerTag ∧ targetNode.isExposed=false) ∧
      Nonempty (GeneralBorrowExposedKnownRootRangeData.Context tree target call.selected call.head call.tail) ∧
      (∀ kind,GeneralRangeMapOrigins.OwnedOn (fun location=>Nonempty
        (GeneralBorrowExposedKnownRootRangeData.Data tree location (ended call).protectedTags target call.selected call.head call.tail kind))
        s.offset (s.offset+s.len) tree.locations) := by
  let target:=expression.data.input.parent
  let expr:=GeneralBorrowFreshMetadataChildDefault.index expression.data.input
  let child:=GeneralBorrowFreshMetadataChildMutable.index call.data.input
  have source:=GeneralBorrowPositiveWildcardWindowAcceptedCallSource.build s updated i stage expression call origin expressionOrigin callOrigin sourceInitialized
  have table:=GeneralBorrowPositiveWildcardWindowAcceptedCallFlags.table s updated call source
  have originalTag:=GeneralBorrowPositiveWildcardWindowAcceptedTargetTag.source s updated i stage expression origin expressionOrigin
  have before:=GeneralBorrowExposedScopedWindowWritableAcceptedGraphMetadata.metadata expression call.toInput callOrigin
  dsimp only at before
  obtain ⟨nodeTags,covered,short,fits,helperLookup,targetNode,exprNode,childNode,targetPresent,targetTag,targetHidden,exprPresent,exprTag,exprHidden,childPresent,childTag,childHidden,paths⟩:=before
  have flags:=GeneralBorrowPositiveWildcardWindowAcceptedUnheld.after_mutable s
  have expressionFree : (ended call).protectedTags.contains exprNode.tag=false := by
    rw [exprTag,←callOrigin.parentTag,source.parentTag,table]
    exact flags.1
  have childFree : (ended call).protectedTags.contains childNode.tag=false := by
    rw [childTag,table,source.tracker]
    exact flags.2
  have restored:=GeneralBorrowCopyGraphRestore.restore (GeneralBorrowExposedScopedWindowWritableAsMutCallReturn.released call.toInput) (copiedTree call) (graph call)
    (ended call).protectedTags child expr target call.selected call.head call.tail s.tracker.global.nextPointerTag nodeTags covered short fits
    targetNode exprNode childNode targetPresent (targetTag.trans originalTag.1) targetHidden exprPresent expressionFree childPresent childFree
    (fun location=>(paths location (ended call).protectedTags).1) context call.offset (call.offset+call.len) owned
  obtain ⟨finalTags,finalCovered,finalShort,finalFits,tagged,hidden,restoredContext,fullOwned⟩:=restored
  rw [source.offset,source.len] at fullOwned
  exact ⟨finalTags,finalCovered,finalShort,finalFits,tagged,hidden,restoredContext,fullOwned⟩
end
end DuplicatePrefix.GeneralBorrowPositiveWildcardWindowAcceptedCopyRestore
