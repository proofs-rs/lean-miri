import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafRun
import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafWrite
import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafExpressionData
namespace DuplicatePrefix.GeneralBorrowExposedScopedDefaultLeafPipeline
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildDefault
open GeneralBorrowExposedKnownRootState (Scope)
variable [area : Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Real parent Read, Default mutable constructor and fresh-child Write on
an arbitrary positive full allocation, from initial scoped leaf resources. -/
theorem run (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedDefaultLeafConstructor.Resources input protections selected head tail)
    (atBase : input.offset = 0) (full : input.len = input.tree.locations.size.bytes) (mode : ChildrenVisitMode) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    let written := child.tree.performBorrowAccessRange (.concrete input.newTag)
      (Size.ofBytes input.offset) (Size.ofBytes input.len) .Write protections mode
    read.status = .Completed ∧ child.outcome = .ok () ∧ written.status = .Completed ∧
      GeneralRangeMapOrigins.OwnedOn
        (fun location => GeneralBorrowExposedKnownRootRangeData.Post .Write written.tree location protections)
        input.offset (input.offset+input.len) written.tree.locations ∧
      written.tree.locations.WellFormed ∧ written.tree.locations.size = input.tree.locations.size := by
  obtain ⟨readDone,next,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,nextRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedDefaultLeafRun.prepare input protections selected head tail raw atBase full mode
  have completed := GeneralBorrowExposedScopedDefaultLeafWrite.construct_write next protections selected head tail nextRaw mode
  obtain ⟨context,owned⟩ := GeneralBorrowExposedScopedDefaultLeafExpressionData.build input protections selected head tail raw
  have nodeFits : input.tree.nodes.data.size ≤ 4294967296 := by
    have aligned := input.aligned
    have fits := input.fits
    omega
  have accessed := GeneralBorrowExposedScopedMixedClosedRange.access input.tree protections input.parentTag input.parent selected head tail
    (Size.ofBytes input.offset) (Size.ofBytes input.len) mode context raw.component.support (fun _=>true) nodeFits
    input.parentTagPresent input.well input.offset (input.offset+input.len) owned input.bounds (Nat.le_refl _) (Nat.le_refl _)
  have readSize : next.tree.locations.size = input.tree.locations.size := by
    rw [treeEq]
    exact accessed.2.2.2
  rw [treeEq] at readSize
  dsimp only at completed ⊢
  simp only [result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq] at completed
  exact ⟨readDone,completed.1,completed.2.1,completed.2.2.1,completed.2.2.2.1,completed.2.2.2.2.trans readSize⟩
end DuplicatePrefix.GeneralBorrowExposedScopedDefaultLeafPipeline
