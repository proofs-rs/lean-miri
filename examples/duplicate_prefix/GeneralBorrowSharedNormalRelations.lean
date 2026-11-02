import duplicate_prefix.GeneralBorrowFreshSharedSlotPaths
import duplicate_prefix.DuplicatePrefixNormalKind
namespace DuplicatePrefix.GeneralBorrowSharedNormalRelations
open Miri Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowAnchor GeneralBorrowFreshSharedPaths
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Every old node has exactly its parent's former scalar relation when
accessed through the fresh shared child. The new leaf is the only new local
node; this law covers actual append and reuse certificates alike. -/
theorem child_old (before after : NormalTreeState) (parent child query : Nat)
    (attachment : Attach before.topology after.topology parent child) (different : query ≠ child) :
    relation after child query = relation before parent query := by
  unfold relation
  rw [attachment.childPath]
  simp only [List.mem_cons,show ¬query = child from different,false_or]

theorem child_self (tree : NormalTreeState) (child : Nat) : relation tree child child = .LocalAccess := by
  simp only [relation,ancestor_self tree.topology child,ite_true]

/-- Existing anchors retain their whole old scalar-relation table. -/
theorem original (before after : NormalTreeState) (parent child anchor query : Nat)
    (attachment : Attach before.topology after.topology parent child)
    (valid : anchor < before.topology.nodes.size) (different : anchor ≠ child) :
    relation after anchor query = relation before anchor query := by
  unfold relation
  rw [attachment.oldPath anchor valid different]

/-- The new child is foreign to every old present source, so an unprotected
shared child can extend that source's original both-kind normal table. -/
theorem original_child_foreign (before after : NormalTreeState) (parent child anchor : Nat)
    (attachment : Attach before.topology after.topology parent child)
    (valid : anchor < before.topology.nodes.size) (different : anchor ≠ child) :
    relation after anchor child = .ForeignAccess := by
  simp only [relation,attachment.outsideOld anchor valid different,ite_false]

end DuplicatePrefix.GeneralBorrowSharedNormalRelations
