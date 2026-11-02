import duplicate_prefix.GeneralBorrowExposedScopedTwoWriteReadRestore
import duplicate_prefix.TypedBorrowSteps
namespace DuplicatePrefix.GeneralBorrowExposedScopedTwoWriteReadFlags
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Exact helper registration and endCall discharge both escaping mutable
layers from an initial high-water bound and their actual source-issued tags. -/
theorem issued_registered_ended (tracker : Miri.Interpreter.MachineHooks.BorrowState) (id : AllocId)
    (bound : Nat) (below : GeneralBorrowProtectedSiblingGenerationBounds.ProtectedBelow tracker.global.protectedTags bound)
    (expr child : BorTag) (issued : bound≤expr.value.toNat) (ordered : expr.value.toNat<child.value.toNat) :
    let held:=TypedBorrowSteps.registeredGlobal tracker child
    let ended:=held.endCall (({} : FrameState).addProtector id child)
    ended.protectedTags.contains expr=false ∧ ended.protectedTags.contains child=false := by
  have free:=GeneralBorrowExposedScopedTwoWriteReadRestore.issued_unheld tracker.global bound below expr issued
  have different : expr≠child := by intro equal;rw [equal] at ordered;omega
  have registered : (TypedBorrowSteps.registeredGlobal tracker child).protectedTags.contains expr=false := by
    change (tracker.global.protectedTags.insert child .StrongProtector).contains expr=false
    unfold ProtectedTags.contains at free ⊢
    rw [ProtectorInsertion.get_other _ child expr _ different]
    exact free
  exact GeneralBorrowExposedScopedTwoWriteReadRestore.ended_unheld (TypedBorrowSteps.registeredGlobal tracker child) id expr child registered
end DuplicatePrefix.GeneralBorrowExposedScopedTwoWriteReadFlags
