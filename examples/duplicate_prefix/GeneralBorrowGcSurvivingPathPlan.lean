import duplicate_prefix.GeneralBorrowGcSurvivingPathPostvisit

namespace DuplicatePrefix.GeneralBorrowGcSurvivingPathPlan
open Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.GeneralBorrowGcWalker DuplicatePrefix.GeneralBorrowGcDfsStage DuplicatePrefix.GeneralBorrowGcStrictChildren
open DuplicatePrefix.GeneralBorrowGcDfsPending DuplicatePrefix.GeneralBorrowGcDfsPlan DuplicatePrefix.GeneralBorrowGcDfsIncoming
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000

/-- Arbitrarily many actual nested postvisits preserve BOTH directions of
parent/child edges, pending-original-node presence/parent/tag and node origins, including real
removals and unary collapses. No postvisit or callback success is assumed. -/
theorem execute (rank : UniIndex → Nat) (original seed : BorrowTree) (root : UniIndex) (live : Array BorTag)
    (metadata : GeneralBorrowGcDfsReadyPlan.Metadata original) (backlinks : Backlinks original) {stack : Array (UniIndex × Nat)} {processed final : List UniIndex} {count : Nat}
    (plan : Plan original stack processed final count) (tree : BorrowTree) (steps : Nat)
    (stage : Stage original processed tree) (ranked : Ranked rank tree)
    (pending : Pending original processed tree)
    (repaired : GeneralBorrowGcDfsReciprocalStage.Reciprocal processed tree)
    (incoming : Incoming original processed tree)
    (paths : GeneralBorrowGcSurvivingPaths.Valid original.nodes tree.nodes)
    (budget : steps+count ≤ tree.nodes.size*2+1) :
    ∃ after, Lean.Loop.forIn {} (none,tree,stack,steps) (outerScan seed root live) =
        (none,after,#[],steps+count) ∧ Stage original final after ∧ Ranked rank after ∧
      Pending original final after ∧ GeneralBorrowGcDfsReciprocalStage.Reciprocal final after ∧ Incoming original final after ∧ after.nodes.size = tree.nodes.size ∧ GeneralBorrowGcSurvivingPaths.Valid original.nodes after.nodes := by
  induction plan generalizing tree steps with
  | done processed =>
    refine ⟨tree,?_,stage,ranked,pending,repaired,incoming,rfl,paths⟩
    rw [Lean.Loop.forIn_eq_of_monadTail]
    simp [outerScan,pure,bind]
  | down stack index cursor node processed final count present unprocessed inside tail ih =>
    have lookup := (stage.outside index unprocessed).trans present
    have actual := GeneralBorrowGcDfsControl.descend seed tree root index node live stack cursor steps lookup inside (by omega)
    obtain ⟨after,execution,finalStage,finalRank,finalPending,finalRepaired,finalIncoming,capacity,finalPaths⟩ := ih tree (steps+1) stage ranked pending repaired incoming paths (by omega)
    refine ⟨after,?_,finalStage,finalRank,finalPending,finalRepaired,finalIncoming,capacity,finalPaths⟩
    rw [Lean.Loop.forIn_eq_of_monadTail,actual]
    simp only [bind]
    have arithmetic : steps+1+count = steps+(count+1) := by omega
    simpa only [arithmetic] using execution
  | up stack index cursor node processed final count present unprocessed finished children tail ih =>
    obtain ⟨middle,actual,middleStage,middleRank,middlePending,middleRepaired,middleIncoming,middleCapacity,middlePaths⟩ := GeneralBorrowGcSurvivingPathPostvisit.step
      rank original seed tree processed root index node live stack cursor steps stage ranked unprocessed present finished children
      (metadata.distinct index node present) (metadata.children index node present) backlinks pending repaired incoming paths (by omega)
    have laterBudget : steps+1+count ≤ middle.nodes.size*2+1 := by rw [middleCapacity];omega
    obtain ⟨after,execution,finalStage,finalRank,finalPending,finalRepaired,finalIncoming,capacity,finalPaths⟩ := ih middle (steps+1) middleStage middleRank middlePending middleRepaired middleIncoming middlePaths laterBudget
    refine ⟨after,?_,finalStage,finalRank,finalPending,finalRepaired,finalIncoming,capacity.trans middleCapacity,finalPaths⟩
    rw [Lean.Loop.forIn_eq_of_monadTail,actual]
    simp only [bind]
    have arithmetic : steps+1+count = steps+(count+1) := by omega
    simpa only [arithmetic] using execution

end DuplicatePrefix.GeneralBorrowGcSurvivingPathPlan
