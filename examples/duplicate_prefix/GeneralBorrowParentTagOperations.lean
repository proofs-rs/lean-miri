import duplicate_prefix.GeneralBorrowParentTagRootFrames
namespace DuplicatePrefix.GeneralBorrowParentTagOperations
open Miri Miri.Memory Miri.ABI Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardParentTagOrder GeneralBorrowExposure
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
/-- Actual ranged access only changes location permissions/cache data, even on
partial failure. Its node array and graph order remain unchanged. -/
theorem access (tree : BorrowTree) (order : ParentTagOrder tree)
    (provenance : ProvenanceExtra) (offset len : Size) (kind : AccessKind)
    (protections : ProtectedTags) (mode : ChildrenVisitMode) :
    ParentTagOrder (tree.performBorrowAccessRange provenance offset len kind protections mode).tree := by
  apply GeneralBorrowParentTagInvariant.nodes_frame tree _ _ order
  cases provenance <;> unfold BorrowTree.performBorrowAccessRange
  all_goals simp only [Id.run,bind,pure]
  all_goals split <;> try simp only [Id.run,bind,pure]
  all_goals split <;> rfl
/-- All actual exposure branches preserve order, including missing tag/node
errors and the already-exposed fast path. -/
theorem expose_all (tree : BorrowTree) (order : ParentTagOrder tree) (depth : ParentDepth tree.nodes)
    (protections : ProtectedTags) (tag : BorTag) : ParentTagOrder (tree.exposeTag protections tag).tree := by
  cases tagged : tree.indexOfTag tag with
  | none => simpa only [BorrowTree.exposeTag,tagged,Id.run,pure] using order
  | some index =>
    cases present : tree.nodeAt index with
    | none => simpa only [BorrowTree.exposeTag,tagged,present,Id.run,pure] using order
    | some node =>
      cases exposed : node.isExposed with
      | false => exact GeneralBorrowParentTagRootFrames.expose tree order tag index node tagged present depth exposed protections
      | true => simpa only [BorrowTree.exposeTag,tagged,present,exposed,↓reduceIte,Id.run,pure] using order
end DuplicatePrefix.GeneralBorrowParentTagOperations
