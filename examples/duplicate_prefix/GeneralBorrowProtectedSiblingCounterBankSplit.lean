import duplicate_prefix.GeneralBorrowSharedBankMutableHistory
namespace DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankSplit
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Split at the first actual tree transition without changing its proof-selected
next state or replacing any generated node data. -/
theorem first {root rootTag offset len} {positive : len ≠ 0} {terminal : BorTag}
    {initial final : GeneralBorrowSharedRootBankState.State root rootTag offset len} {action rest}
    (history : GeneralBorrowSharedBankMutableHistory.Run positive terminal initial (action::rest) final) :
    ∃ middle,GeneralBorrowSharedBankMutableHistory.Run positive terminal initial [action] middle ∧
      GeneralBorrowSharedBankMutableHistory.Run positive terminal middle rest final := by
  cases history with
  | borrow state tag position rest valid fresh room readDone childDone later =>
    refine ⟨_,?_,later⟩
    exact .borrow initial tag position [] valid fresh room readDone childDone (.nil _)
  | mutable state tag rest fresh room completed later =>
    refine ⟨_,?_,later⟩
    exact .mutable initial tag [] fresh room completed (.nil _)
  | gc state extra rest fresh completed later =>
    refine ⟨_,?_,later⟩
    exact .gc initial extra [] fresh completed (.nil _)
  | exposeRoot state rest completed later =>
    refine ⟨_,?_,later⟩
    exact .exposeRoot initial [] completed (.nil _)
  | rootAccess state kind rest fresh completed later =>
    refine ⟨_,?_,later⟩
    exact .rootAccess initial kind [] fresh completed (.nil _)
end DuplicatePrefix.GeneralBorrowProtectedSiblingCounterBankSplit
