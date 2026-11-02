import duplicate_prefix.GeneralBorrowExposedScopedDefaultLeafRun
import duplicate_prefix.GeneralBorrowFreshDefaultGeometry
import duplicate_prefix.GeneralBorrowStructuralAccessGeometry
namespace DuplicatePrefix.GeneralBorrowExposedScopedDefaultLeafNextGeometry
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowFreshMetadataChildDefault
variable [area : GeneralBorrowExposedKnownRootState.Scope]
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
/-- Actual full-range expression Read and Default construction preserve the
allocation byte partition, so the next helper still borrows the full range. -/
theorem frame (input : Input) (protections : ProtectedTags) (selected head : UniIndex) (tail : List UniIndex)
    (raw : GeneralBorrowExposedScopedDefaultLeafConstructor.Resources input protections selected head tail)
    (atBase : input.offset=0) (full : input.len=input.tree.locations.size.bytes) (mode : ChildrenVisitMode) :
    let read := input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode
    let child := read.tree.newChild (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
      (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false
    child.tree.locations.WellFormed ∧ child.tree.locations.size=input.tree.locations.size := by
  obtain ⟨done,prepared,treeEq,parentTagEq,newTagEq,parentEq,offsetEq,lenEq,indexEq,preparedRaw,supportEq⟩ :=
    GeneralBorrowExposedScopedDefaultLeafRun.prepare input protections selected head tail raw atBase full mode
  have geometry := GeneralBorrowFreshDefaultGeometry.append_frame prepared
  have readGeometry := GeneralBorrowStructuralAccessGeometry.access input.tree (.concrete input.parentTag)
    (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode input.well input.bounds
  have childEq : result prepared =
      ((input.tree.performBorrowAccessRange (.concrete input.parentTag) (Size.ofBytes input.offset) (Size.ofBytes input.len) .Read protections mode).tree.newChild
        (Size.ofBytes input.offset) (.concrete input.parentTag) input.newTag
        (DedupRangeMap.new (Size.ofBytes input.len) GeneralBorrowFreshDefaultChild.inside) (.ReservedFrz false) false).tree := by
    simp only [result,treeEq,parentTagEq,newTagEq,offsetEq,lenEq]
  rw [childEq] at geometry
  exact ⟨geometry.1,geometry.2.trans (by rw [treeEq];exact readGeometry.2)⟩
end DuplicatePrefix.GeneralBorrowExposedScopedDefaultLeafNextGeometry
