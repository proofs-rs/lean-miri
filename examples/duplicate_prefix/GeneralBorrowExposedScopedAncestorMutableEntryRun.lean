import duplicate_prefix.GeneralBorrowExposedScopedAncestorDefaultRun
import duplicate_prefix.GeneralBorrowFreshChild
namespace DuplicatePrefix.GeneralBorrowExposedScopedAncestorMutableEntryRun
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildDefault
open GeneralBorrowExposedScopedAncestorDefaultConstructor (Resources)
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Actual ancestor-aware parent Read and protected mutable FnEntry append.
The shared/unprotected Default posttree is never substituted for this child. -/
theorem append (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : Resources input protections selected head tail)
    (atBase : input.offset=0) (full : input.len=input.tree.locations.size.bytes) :
    let read:=input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len)
      .Read protections .VisitChildrenOfAccessed
    let child:=read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshChild.inside) (.ReservedFrz false) true
    read.status=.Completed ∧ child.outcome=.ok () := by
  obtain ⟨readDone,next,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,nextRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedAncestorDefaultRun.prepare input protections selected head tail raw atBase full
  have childDone := GeneralBorrowFreshChild.mutable_success next.tree next.depth next.parentTag next.newTag next.parent next.parentNode
    next.parentTagPresent next.parentPresent next.fresh next.noFree next.aligned next.fits next.offset next.len next.nonzero next.well next.bounds
  exact ⟨readDone,by simpa only [treeEq,parentTagEq,newTagEq,offsetEq,lenEq] using childDone⟩
end DuplicatePrefix.GeneralBorrowExposedScopedAncestorMutableEntryRun
