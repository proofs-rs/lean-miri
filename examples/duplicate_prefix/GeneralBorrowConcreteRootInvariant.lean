import duplicate_prefix.GeneralBorrowConcreteRowAccess
namespace DuplicatePrefix.GeneralBorrowConcreteRootInvariant
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowConcreteRowAccess (State scan)
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000

/-- Pure invariant adapter for the actual indexed root scan. Its callback
interface is discharged from raw data by each operational wrapper. -/
theorem roots (tree : BorrowTree) (protections : ProtectedTags) (selected : UniIndex)
    (maximum minimum : Option BorTag) (kind : AccessKind) (mode : ChildrenVisitMode) (range : ByteRange)
    (property : LocationTree → Prop)
    (callback : ∀ position (valid : position < tree.roots.size), selected ≠ tree.roots[position] →
      ∀ location, property location →
      let result := tree.performWildcardAccessAt location tree.roots[position] maximum kind protections (position != 0)
      result.status = .Completed ∧ property result.location)
    (initial : State) (good : initial.2.1 = none ∧ property initial.1) :
    let result : Id State := forIn (List.range' 0 tree.roots.size) initial
      (scan tree selected maximum minimum kind protections mode range)
    result.2.1 = none ∧ property result.1 := by
  apply GeneralBorrowLoop.list_invariant _ _ (fun state : State => state.2.1 = none ∧ property state.1) _ initial good
  intro position member state good
  rcases state with ⟨location,status,stop⟩
  rcases good with ⟨statusEq,validProperty⟩
  dsimp only at statusEq
  subst status
  have valid : position < tree.roots.size := by
    have bounded := List.mem_range'_1.mp member
    simpa using bounded.2
  have lookup := Array.getElem?_eq_getElem valid
  by_cases stopped : stop = true
  · subst stop
    simpa [scan,Id.run,bind,pure] using (show (none : Option BorrowTree.BorrowTreeAccessStatus) = none ∧ property location from ⟨rfl,validProperty⟩)
  have stopFalse : stop = false := by cases stop <;> simp_all
  subst stop
  by_cases same : selected = tree.roots[position]
  · simp [scan,Id.run,pure,lookup,same,apply_ite,validProperty]
  · have preserved := callback position valid same location validProperty
    simp [scan,Id.run,pure,lookup,same,preserved.1,apply_ite,validProperty,preserved.2]
end DuplicatePrefix.GeneralBorrowConcreteRootInvariant
