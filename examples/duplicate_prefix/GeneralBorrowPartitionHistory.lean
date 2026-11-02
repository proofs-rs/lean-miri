import duplicate_prefix.GeneralBorrowPartitionState

namespace DuplicatePrefix.GeneralBorrowPartitionHistory
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowPartitionState
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

set_option autoImplicit false in
/-- An actual Read or Write request, with explicit allocation bounds. Zero
length is permitted; no successful access is included in this input. -/
structure Action (bytes : UInt64) where
  offset : UInt64
  len : UInt64
  kind : AccessKind
  bounds : offset.toNat+len.toNat ≤ bytes.toNat

def next (tree : BorrowTree) (tag : BorTag) {bytes : UInt64} (action : Action bytes) : BorrowTree :=
  (operation tree tag action.offset action.len action.kind).tree

def execute (tree : BorrowTree) (tag : BorTag) {bytes : UInt64} : List (Action bytes) → BorrowTree
  | [] => tree
  | action :: rest => execute (next tree tag action) tag rest

def AllCompleted (tree : BorrowTree) (tag : BorTag) {bytes : UInt64} : List (Action bytes) → Prop
  | [] => True
  | action :: rest => (operation tree tag action.offset action.len action.kind).status = .Completed ∧
      AllCompleted (next tree tag action) tag rest

/-- Arbitrary finite in-bounds partial-range Reads and Writes retain enough
ownership and vacant Clean for a later whole invocation. Actual preparation,
interval splitting, differing permissions and write-back are all included. -/
theorem run (tree : BorrowTree) (root : UniIndex) (bytes : UInt64) (tag : BorTag)
    (s : State tree root bytes) (tagged : s.node.tag = tag) (actions : List (Action bytes)) :
    AllCompleted tree tag actions ∧
    Nonempty {post : State (execute tree tag actions) root bytes // post.node.tag = tag} ∧
    (execute tree tag actions).nodes = tree.nodes ∧
    (execute tree tag actions).tagMapping = tree.tagMapping := by
  induction actions generalizing tree with
  | nil => exact ⟨True.intro,⟨⟨s,tagged⟩⟩,rfl,rfl⟩
  | cons action rest ih =>
    have facts := access tree root bytes s action.offset action.len action.kind action.bounds
    rw [tagged] at facts
    obtain ⟨⟨post,postTag⟩⟩ := facts.2.1
    have tail := ih _ post postTag
    have frame := GeneralBorrowFreshReadFrame.frame tree (.concrete tag) (Size.ofBytes action.offset)
      (Size.ofBytes action.len) action.kind {} .VisitChildrenOfAccessed
    have nodes : (next tree tag action).nodes = tree.nodes := by simpa only [next,operation,BorrowTree.performNormalAccessRange] using congrArg BorrowTree.nodes frame
    exact ⟨⟨facts.1,tail.1⟩,tail.2.1,tail.2.2.1.trans nodes,tail.2.2.2.trans facts.2.2.2⟩

end DuplicatePrefix.GeneralBorrowPartitionHistory
