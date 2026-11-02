import duplicate_prefix.GeneralBorrowGcSharedRootBank
namespace DuplicatePrefix.GeneralBorrowSharedBankGcAction
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

inductive Action where
  | borrow (tag : BorTag) (position : Nat)
  | gc (extraLive : Array BorTag)

def tags : List Action → List BorTag
  | [] => []
  | .borrow tag _ :: rest => tag :: tags rest
  | .gc _ :: rest => tags rest

def Choices : Nat → List Action → Prop
  | _,[] => True
  | count,.borrow _ position :: rest => position < count ∧ Choices (count+1) rest
  | count,.gc _ :: rest => Choices count rest

/-- Actual handle tags are appended to arbitrary caller liveness. No retained
handle premise, exposed flag or cache-correctness assumption is needed. -/
def live {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (extra : Array BorTag) : Array BorTag :=
  extra ++ (s.bank.handles.filterMap fun index => (s.bank.tree.nodes.get index).map TreeNode.tag).toArray

theorem live_handles {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (extra : Array BorTag) :
    GeneralBorrowGcSharedBank.Live s.bank (live s extra) := by
  intro index member node present
  apply Array.contains_iff_mem.mpr
  apply Array.mem_append.mpr
  right
  apply List.mem_toArray.mpr
  exact List.mem_filterMap.mpr ⟨index,member,by rw [present];rfl⟩

def next {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (positive : len ≠ 0)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (extra : Array BorTag) :=
  GeneralBorrowGcSharedRootBank.next s positive tag fresh (live s extra) (live_handles s extra)

theorem tree {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (positive : len ≠ 0)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (extra : Array BorTag) :
    (next s positive tag fresh extra).bank.tree = (s.bank.tree.removeUnreachableTags (live s extra)).tree := by
  exact (GeneralBorrowGcSharedBank.collect s positive (live s extra) (live_handles s extra)).property.1

theorem handles {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (positive : len ≠ 0)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (extra : Array BorTag) :
    (next s positive tag fresh extra).bank.handles = s.bank.handles := by
  exact (GeneralBorrowGcSharedBank.collect s positive (live s extra) (live_handles s extra)).property.2.1

theorem completed {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (positive : len ≠ 0) (extra : Array BorTag) :
    (s.bank.tree.removeUnreachableTags (live s extra)).outcome = .ok () :=
  (GeneralBorrowGcSharedBank.collect s positive (live s extra) (live_handles s extra)).property.2.2

theorem size {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (positive : len ≠ 0)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (extra : Array BorTag) :
    (next s positive tag fresh extra).bank.tree.nodes.size = s.bank.tree.nodes.size := by
  rw [tree]
  exact (GeneralBorrowGcResourceFrame.preserves (n := 0) (fun i => Fin.elim0 i) s.bank.tree (live s extra) (by intro i;exact Fin.elim0 i)).capacity

theorem fresh_tag {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (positive : len ≠ 0)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (extra : Array BorTag)
    (future : BorTag) (available : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping future) :
    GeneralBorrowTagMap.Fresh (next s positive tag fresh extra).bank.tree.tagMapping future := by
  rw [tree]
  exact (GeneralBorrowGcResourceFrame.preserves (n := 1) (fun _ => future) s.bank.tree (live s extra) (fun _ => available)).fresh 0
end
end DuplicatePrefix.GeneralBorrowSharedBankGcAction
