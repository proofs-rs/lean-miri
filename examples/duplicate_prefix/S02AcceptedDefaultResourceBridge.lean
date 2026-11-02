import duplicate_prefix.S02AcceptedDefaultReadyRuntime
import duplicate_prefix.GeneralBorrowRawDefaultFrameLedger

namespace DuplicatePrefix.S02AcceptedDefaultResourceBridge
open Miri Miri.Memory Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
noncomputable section

/-- The two shared borrow constructors leave enough room for the two mutable
constructors used by the real Default/as_mut suffix. -/
theorem after_shared
    (source finalTree : BorrowTree)
    (tracker held : MachineHooks.BorrowState) (selected : UniIndex)
    (graph : GeneralBorrowRawSharedToLenLedger.Graph source finalTree
      selected tracker held)
    (nodeMargin : source.nodes.size + 4 < 65536)
    (tagMargin : tracker.global.nextPointerTag.value.toNat + 3 < 18446744073709551615) :
    finalTree.nodes.size + 2 < 65536 ∧
    held.global.nextPointerTag.value.toNat + 1 < 18446744073709551615 := by
  have growth := graph.growth
  have counter := graph.tagCounter
  omega

end
end DuplicatePrefix.S02AcceptedDefaultResourceBridge

open Lean Elab Command in
run_cmd do
  for dependency in (← collectAxioms ``DuplicatePrefix.S02AcceptedDefaultResourceBridge.after_shared) do
    unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
      throwError "unapproved Default resource bridge dependency {dependency}"
