import duplicate_prefix.GeneralBorrowRetainedMutableAccess
namespace DuplicatePrefix.GeneralBorrowRetainedMutableAccessFacts
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowRetainedMutableAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
noncomputable section

theorem build_mapping {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (kind : AccessKind) :
    (build s kind).state.tree.tagMapping=s.tree.tagMapping := by
  rw [(build s kind).actual]
  have equal := congrArg BorrowTree.tagMapping (GeneralBorrowFreshReadFrame.frame s.tree (.concrete childTag)
    (Size.ofBytes offset) (Size.ofBytes len) kind {} .VisitChildrenOfAccessed)
  exact equal

theorem build_nodes {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (kind : AccessKind) :
    (build s kind).state.tree.nodes=s.tree.nodes := by
  rw [(build s kind).actual]
  have equal := congrArg BorrowTree.nodes (GeneralBorrowFreshReadFrame.frame s.tree (.concrete childTag)
    (Size.ofBytes offset) (Size.ofBytes len) kind {} .VisitChildrenOfAccessed)
  exact equal

theorem run_mapping {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (kinds : List AccessKind) :
    (run s kinds).tree.tagMapping=s.tree.tagMapping := by
  induction kinds generalizing s with
  | nil => rfl
  | cons kind rest ih => exact (ih (build s kind).state).trans (build_mapping s kind)

theorem run_nodes {root child : UniIndex} {childTag : BorTag} {offset len : UInt64}
    (s : State root child childTag offset len) (kinds : List AccessKind) :
    (run s kinds).tree.nodes=s.tree.nodes := by
  induction kinds generalizing s with
  | nil => rfl
  | cons kind rest ih => exact (ih (build s kind).state).trans (build_nodes s kind)

theorem ofEpisode_tree {root : UniIndex} {rootTag : BorTag} {offset len : UInt64}
    (s : GeneralBorrowSharedRootBankState.State root rootTag offset len) (tag : BorTag)
    (fresh : GeneralBorrowTagMap.Fresh s.bank.tree.tagMapping tag) (nonzero : len≠0)
    (room : s.bank.tree.nodes.size+5≤4294967295) :
    (ofEpisode s tag fresh nonzero room).tree=(GeneralBorrowRetainedMutableEpisode.operation s tag).tree :=
  (GeneralBorrowRetainedMutableEpisode.build s tag fresh nonzero room).actual
end
end DuplicatePrefix.GeneralBorrowRetainedMutableAccessFacts
