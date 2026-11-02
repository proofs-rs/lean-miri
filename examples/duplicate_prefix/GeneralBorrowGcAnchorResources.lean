import duplicate_prefix.GeneralBorrowGcAnchorOwnership
import duplicate_prefix.GeneralBorrowGcRootResources
namespace DuplicatePrefix.GeneralBorrowGcAnchorResources
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowProjection DuplicatePrefix.GeneralRangeMapOrigins
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

set_option autoImplicit false in
/-- Actual collected finite-forest resources and a retained arbitrary anchor's
Read/Write ownership. No successful-operation field is an input. -/
structure Collected (tree : BorrowTree) (root anchor : UniIndex) (tag : BorTag)
    (kind : AccessKind) (lower upper : UInt64) (live : Array BorTag) where
  resources : GeneralBorrowRecursiveSharedResources.Resources (tree.removeUnreachableTags live).tree root
  node : TreeNode
  present : (tree.removeUnreachableTags live).tree.nodes.get anchor = some node
  tagged : node.tag = tag
  owned : OwnedOn (GeneralBorrowRange.LocationOwned (tree.removeUnreachableTags live).tree {} anchor kind)
    lower upper (tree.removeUnreachableTags live).tree.locations
  completed : (tree.removeUnreachableTags live).outcome = .ok ()
  capacity : (tree.removeUnreachableTags live).tree.locations.size = tree.locations.size

/-- Full real GC forms a retained arbitrary CHILD anchor's next-operation
resources from initial finite-forest data, source tag liveness and slice ownership.
Its exact sparse index and original tag survive; contraction of other ancestors
is handled by exact surviving path equivalence, not a final ownership premise. -/
def collect (tree : BorrowTree) (root : UniIndex)
    (s : GeneralBorrowRecursiveSharedResources.Resources tree root)
    (location : LocationTree)
    (forest : GeneralBorrowForest.Forest (source_normal_projection tree location {}).topology)
    (roots : ∀ index ∈ tree.roots.toList, ∃ node, tree.nodes.get index = some node ∧ node.parent = none)
    (anchor : UniIndex) (node : TreeNode) (present : tree.nodes.get anchor = some node)
    (live : Array BorTag) (held : live.contains node.tag = true)
    (kind : AccessKind) (lower upper : UInt64)
    (owned : OwnedOn (GeneralBorrowRange.LocationOwned tree {} anchor kind) lower upper tree.locations) :
    Collected tree root anchor node.tag kind lower upper live := by
  have fits : tree.nodes.size ≤ 4294967296 := by have room := s.room;omega
  have complete := GeneralBorrowGcForestComplete.complete tree location {} forest s.depth s.children fits roots s.well live
  have restored := GeneralBorrowGcAnchorOwnership.collect tree location {} forest s.depth s.children fits roots s.well live
    anchor node present held kind lower upper owned s.clean
  let current := Classical.choose restored.2
  have facts := Classical.choose_spec restored.2
  have frame := GeneralBorrowGcResourceFrame.preserves (n := 0) (fun i => Fin.elim0 i) tree live (by intro i;exact Fin.elim0 i)
  exact {
    resources := {
      depth := Classical.choice complete.2.2.2.2.1
      children := complete.2.2.2.2.2.2.1
      covered := GeneralBorrowGcNodeMetadata.roots_cover tree live s.covered
      roots := frame.roots.trans s.roots
      allocator := GeneralBorrowGcAllocatorFull.preserves tree live s.allocator
      clean := GeneralBorrowGcFullClean.preserves tree live s.clean
      well := complete.2.1
      room := by rw [frame.capacity];exact s.room }
    node := current,present := facts.1,tagged := facts.2.1,owned := facts.2.2
    completed := restored.1,capacity := complete.2.2.1 }
end
end DuplicatePrefix.GeneralBorrowGcAnchorResources
