import duplicate_prefix.GeneralBorrowProtectedSiblingCounterBankRun
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankGrowth
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowSharedBankMutableAction GeneralBorrowProtectedSiblingCounterBank
set_option maxRecDepth 65536
set_option maxHeartbeats 6000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem bank {root rootTag offset len} {positive : len ≠ 0} {terminal : BorTag}
    {initial final : GeneralBorrowSharedRootBankState.State root rootTag offset len} {actions}
    (history : GeneralBorrowSharedBankMutableHistory.Run positive terminal initial actions final) :
    final.bank.tree.nodes.size ≤ initial.bank.tree.nodes.size+(tags actions).length := by
  induction history with
  | nil => simp [tags]
  | borrow s tag position rest valid fresh room _ _ tail ih =>
    have growth := GeneralBorrowSharedRootBankAdvance.size s (GeneralBorrowSharedRootBankHistory.parent s position valid) (GeneralBorrowSharedRootBankHistory.parent_mem s position valid) tag fresh positive room
    simp only [tags,List.length_cons]
    omega
  | mutable s tag rest fresh room _ tail ih =>
    have growth := GeneralBorrowSharedRootMutableEpisode.size s tag fresh positive room
    simp only [tags,List.length_cons]
    omega
  | gc s extra rest fresh _ tail ih =>
    have same := GeneralBorrowSharedBankGcAction.size s positive terminal fresh extra
    simp only [tags]
    omega
  | exposeRoot s rest _ tail ih =>
    have same := GeneralBorrowSharedRootBankExposure.size s
    simp only [tags]
    omega
  | rootAccess s kind rest fresh _ tail ih =>
    have same := GeneralBorrowSharedRootAccess.size s terminal fresh kind
    simp only [tags]
    omega

theorem allocation {global advanced instructions actions}
    (actual : Allocation global instructions actions advanced) : (tags actions).length=allocations instructions := by
  induction actual <;> simp_all [tags,allocations]

theorem run {root rootTag offset len} {positive : len ≠ 0} {terminal : BorTag}
    {initial final : GeneralBorrowSharedRootBankState.State root rootTag offset len}
    {global advanced instructions}
    (history : GeneralBorrowProtectedSiblingCounterBankRun.Run positive terminal global initial instructions advanced final) :
    final.bank.tree.nodes.size ≤ initial.bank.tree.nodes.size+allocations instructions := by
  induction history with
  | nil => simp [allocations]
  | @step global advanced finalGlobal initial middle finalState instruction action rest allocated _ actual tail ih =>
    have growth := bank actual
    have count := allocation allocated
    have add : allocations (instruction::rest) = allocations [instruction]+allocations rest := by
      cases instruction <;> simp [allocations,Nat.add_comm]
    rw [add]
    omega
end DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankGrowth
