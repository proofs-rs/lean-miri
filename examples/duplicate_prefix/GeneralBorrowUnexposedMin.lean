import duplicate_prefix.BorrowRangeAccess
import duplicate_prefix.GeneralBorrowLoop

namespace DuplicatePrefix.GeneralBorrowUnexposedMin
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- With every present node unexposed, the real bounded source search returns
none for any start. No graph well-formedness or successful traversal is assumed. -/
theorem min_none (tree : BorrowTree) (anchor : UniIndex)
    (unexposed : ∀ index node, tree.nodes.get index = some node → node.isExposed = false) :
    source_min_exposed tree anchor = none := by
  unfold_min_exposed
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  let property := fun state : Option (Option BorTag) × Array UniIndex × Nat × Option BorTag =>
    (∀ result, state.1 = some result → result = none) ∧ state.2.2.2 = none
  let measure := fun state : Option (Option BorTag) × Array UniIndex × Nat × Option BorTag => tree.nodes.size+1-state.2.2.1
  have step : ∀ state, property state →
      (∃ final, scan () state = .done final ∧ property final) ∨
      ∃ next, scan () state = .yield next ∧ property next ∧ measure next < measure state := by
    intro state good
    rcases state with ⟨returned,stack,steps,minimum⟩
    have minimumEq : minimum = none := good.2
    subst minimum
    by_cases guard : (!stack.isEmpty && decide (steps ≤ tree.nodes.size)) = true
    · have bound : steps ≤ tree.nodes.size := of_decide_eq_true (Bool.and_eq_true_iff.mp guard).2
      cases back : stack.back? with
      | none =>
        exact .inl ⟨(some none,stack,steps+1,none),by simp only [scan,guard,back,ite_true],by simp [property]⟩
      | some index =>
        cases present : tree.nodes.get index with
        | none =>
          refine .inr ⟨(none,stack.pop,steps+1,none),by simp only [scan,guard,back,present,ite_true],by simp [property],?_⟩
          dsimp only [measure]
          omega
        | some node =>
          have flag := unexposed index node present
          let nextStack := forIn' node.children stack.pop (fun child _ current => (pure (.yield (current.push child)) : Id (ForInStep (Array UniIndex))))
          refine .inr ⟨(none,nextStack,steps+1,none),?_,by simp [property],?_⟩
          · simp only [scan,guard,back,present,flag,ite_true,Option.any_none,Bool.not_false,Bool.false_and,Bool.false_eq_true,ite_false]
            rfl
          · dsimp only [measure]
            omega
    · exact .inl ⟨(none,stack,steps,none),by simp only [scan,guard,Bool.false_eq_true,ite_false],by simp [property]⟩
  have initial : property (none,#[anchor],0,none) := by simp [property]
  have final := GeneralBorrowLoop.invariant scan measure property step (none,#[anchor],0,none) initial
  cases returned : (Lean.Loop.forIn {} (none,#[anchor],0,none) scan).1 with
  | none => simpa only [returned] using final.2
  | some result => simpa only [returned] using final.1 result returned

end DuplicatePrefix.GeneralBorrowUnexposedMin
