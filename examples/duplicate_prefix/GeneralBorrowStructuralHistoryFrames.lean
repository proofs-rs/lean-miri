import duplicate_prefix.GeneralBorrowStructuralHistoryState
import duplicate_prefix.GeneralBorrowStructuralAccessGeometry
import duplicate_prefix.GeneralBorrowRootExposureFrame
import duplicate_prefix.GeneralBorrowStructuralReleaseGeometryFrame
namespace DuplicatePrefix.GeneralBorrowStructuralHistoryFrames
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowStructuralHistoryState
set_option maxRecDepth 65536
set_option maxHeartbeats 1500000

/-- Both read/write kinds, concrete/wildcard sources, every child visit mode,
and either outcome retain intrinsic graph and partition invariants. This is a
structural assertion; failing accesses remain failing accesses. -/
theorem access (tree : BorrowTree) (initial : State tree) (provenance : ProvenanceExtra) (offset len : Size)
    (kind : AccessKind) (protections : ProtectedTags) (mode : ChildrenVisitMode)
    (bounds : offset.bytes.toNat+len.bytes.toNat≤tree.locations.size.bytes.toNat) :
    State (tree.performBorrowAccessRange provenance offset len kind protections mode).tree ∧
    (tree.performBorrowAccessRange provenance offset len kind protections mode).tree.locations.size=tree.locations.size := by
  have frame := GeneralBorrowFreshReadFrame.frame tree provenance offset len kind protections mode
  have geometry := GeneralBorrowStructuralAccessGeometry.access tree provenance offset len kind protections mode initial.well bounds
  refine ⟨⟨?_,geometry.1⟩,geometry.2⟩
  rw [frame]
  exact graph_locations tree _ initial.toGraphState

/-- Actual exposure preserves structural state, including missing-tag/node
errors. When a node exists, its real exposure/cache updates are performed. -/
theorem expose (tree : BorrowTree) (initial : State tree) (tag : BorTag) (protections : ProtectedTags) :
    State (tree.exposeTag protections tag).tree ∧
    (tree.exposeTag protections tag).tree.locations.size=tree.locations.size := by
  cases tagged : tree.indexOfTag tag with
  | none => simpa [BorrowTree.exposeTag,tagged] using And.intro initial (rfl : tree.locations.size=tree.locations.size)
  | some index =>
    cases present : tree.nodeAt index with
    | none => simpa [BorrowTree.exposeTag,tagged,present] using And.intro initial (rfl : tree.locations.size=tree.locations.size)
    | some node =>
      cases exposed : node.isExposed with
      | true => simpa [BorrowTree.exposeTag,tagged,present,exposed] using And.intro initial (rfl : tree.locations.size=tree.locations.size)
      | false =>
        obtain ⟨depth⟩ := initial.depth
        have shape := (GeneralBorrowRootExposureFrame.expose tree tag index node tagged present depth exposed protections).2.1
        exact ⟨GeneralBorrowStructuralHistoryState.shape tree _ shape initial,
          (GeneralBorrowFreshGeometry.shape_frame tree _ shape initial.well).2⟩
/-- The real implicit protector-end access and exposure-cache phase retain
structural state on all outcomes, including a failing partial prefix. -/
theorem release (tree : BorrowTree) (initial : State tree) (tag : BorTag) (protections : ProtectedTags) :
    State (tree.releaseProtector tag protections).tree ∧
    (tree.releaseProtector tag protections).tree.locations.size=tree.locations.size := by
  have frame := GeneralBorrowStructuralReleaseGeometryFrame.release tree protections tag
  have geometry := GeneralBorrowStructuralReleaseGeometry.release tree protections tag initial.well
  refine ⟨⟨?_,geometry.1⟩,geometry.2⟩
  rw [frame]
  exact graph_locations tree _ initial.toGraphState
end DuplicatePrefix.GeneralBorrowStructuralHistoryFrames
