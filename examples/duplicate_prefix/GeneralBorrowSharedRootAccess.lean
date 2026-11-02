import duplicate_prefix.GeneralBorrowSharedRootRead
namespace DuplicatePrefix.GeneralBorrowSharedRootAccess
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

def count (kind : AccessKind) (before : Nat) : Nat := match kind with
  | .Read => before
  | .Write => 1

def next {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (kind : AccessKind) :=
  match kind with
  | .Read => (GeneralBorrowSharedRootRead.build s tag fresh).state
  | .Write => (GeneralBorrowSharedRootAccessReset.build s tag fresh .Write).state

theorem tree {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (kind : AccessKind) :
    (next s tag fresh kind).bank.tree = (GeneralBorrowSharedRootAccessReset.operation s kind).tree := by
  cases kind with
  | Read => exact (GeneralBorrowSharedRootRead.build s tag fresh).actual
  | Write => exact (GeneralBorrowSharedRootAccessReset.build s tag fresh .Write).actual

theorem handles {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (kind : AccessKind) :
    (next s tag fresh kind).bank.handles.length = count kind s.bank.handles.length := by
  cases kind with
  | Read => exact congrArg List.length (GeneralBorrowSharedRootRead.build s tag fresh).handles
  | Write =>
    change (GeneralBorrowSharedRootAccessReset.build s tag fresh .Write).state.bank.handles.length = 1
    rw [(GeneralBorrowSharedRootAccessReset.build s tag fresh .Write).handles]
    rfl

theorem completed {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (kind : AccessKind) :
    (GeneralBorrowSharedRootAccessReset.operation s kind).status = .Completed := by
  cases kind with
  | Read => exact (GeneralBorrowSharedRootRead.build s tag fresh).completed
  | Write => exact (GeneralBorrowSharedRootAccessReset.build s tag fresh .Write).completed

theorem size {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (kind : AccessKind) :
    (next s tag fresh kind).bank.tree.nodes.size = s.bank.tree.nodes.size := by
  rw [tree]
  have frame := GeneralBorrowFreshReadFrame.frame s.bank.tree (.concrete rootTag) (Size.ofBytes offset) (Size.ofBytes len) kind {} .VisitChildrenOfAccessed
  have equal := congrArg (fun result : BorrowTree => result.nodes.size) frame
  exact equal

theorem fresh_tag {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len)
    (tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (kind : AccessKind)
    (future : BorTag) (available : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping future) :
    GeneralBorrowTagMap.Fresh (next s tag fresh kind).bank.tree.tagMapping future := by
  rw [tree]
  have frame := GeneralBorrowFreshReadFrame.frame s.bank.tree (.concrete rootTag) (Size.ofBytes offset) (Size.ofBytes len) kind {} .VisitChildrenOfAccessed
  have mapping := congrArg BorrowTree.tagMapping frame
  change (GeneralBorrowSharedRootAccessReset.operation s kind).tree.tagMapping = s.bank.tree.tagMapping at mapping
  rw [mapping]
  exact available
end
end DuplicatePrefix.GeneralBorrowSharedRootAccess
