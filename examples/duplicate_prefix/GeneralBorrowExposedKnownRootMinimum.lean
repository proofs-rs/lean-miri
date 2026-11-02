import duplicate_prefix.BorrowRangeAccess
import duplicate_prefix.GeneralBorrowLoop

namespace DuplicatePrefix.GeneralBorrowExposedKnownRootMinimum
open Miri.ABI Miri.Memory Miri.DataStructures Miri.TreeBorrows Miri.TreeBorrows.Tree
open DuplicatePrefix.BorrowRangeAccess
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- A child-closed hidden selected component derives no minimum exposure even
when other physical components are exposed. The source bound/error paths are retained. -/
theorem min_none (tree : BorrowTree) (anchor : UniIndex) (support : UniIndex → Prop)
    (rooted : support anchor)
    (children : ∀ index node,support index → tree.nodes.get index = some node → ∀ child ∈ node.children.toList,support child)
    (unexposed : ∀ index node,support index → tree.nodes.get index = some node → node.isExposed = false) :
    source_min_exposed tree anchor = none := by
  unfold_min_exposed
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  let property := fun state : Option (Option BorTag) × Array UniIndex × Nat × Option BorTag =>
    (∀ result, state.1 = some result → result = none) ∧ state.2.2.2 = none ∧ ∀ index ∈ state.2.1.toList,support index
  let measure := fun state : Option (Option BorTag) × Array UniIndex × Nat × Option BorTag => tree.nodes.size+1-state.2.2.1
  have step : ∀ state, property state →
      (∃ final, scan () state = .done final ∧ property final) ∨
      ∃ next, scan () state = .yield next ∧ property next ∧ measure next < measure state := by
    intro state good
    rcases state with ⟨returned,stack,steps,minimum⟩
    have minimumEq : minimum = none := good.2.1
    subst minimum
    by_cases guard : (!stack.isEmpty && decide (steps ≤ tree.nodes.size)) = true
    · have bound : steps ≤ tree.nodes.size := of_decide_eq_true (Bool.and_eq_true_iff.mp guard).2
      cases back : stack.back? with
      | none =>
        exact .inl ⟨(some none,stack,steps+1,none),by simp only [scan,guard,back,ite_true],by exact ⟨by simp,rfl,good.2.2⟩⟩
      | some index =>
        cases present : tree.nodes.get index with
        | none =>
          refine .inr ⟨(none,stack.pop,steps+1,none),by simp only [scan,guard,back,present,ite_true],by
            refine ⟨by simp,rfl,?_⟩
            intro query member
            exact good.2.2 query ((List.dropLast_subset stack.toList (by simpa only [Array.toList_pop] using member))) ,?_⟩
          dsimp only [measure]
          omega
        | some node =>
          have member : index ∈ stack.toList := Array.mem_def.mp (Array.mem_of_back? back)
          have supported := good.2.2 index member
          have flag := unexposed index node supported present
          let nextStack := forIn' node.children stack.pop (fun child _ current => (pure (.yield (current.push child)) : Id (ForInStep (Array UniIndex))))
          have pushed : nextStack = stack.pop ++ node.children := by
            dsimp only [nextStack]
            rw [Array.forIn'_pure_yield_eq_foldl]
            change node.children.attach.foldl (fun current child => current.push child.val) stack.pop = _
            rw [Array.foldl_push_eq_append rfl]
            simpa only [Array.map_id'] using congrArg (fun rows => stack.pop ++ rows) (Array.attach_map_val node.children (fun child => child))
          refine .inr ⟨(none,nextStack,steps+1,none),?_,?_,?_⟩
          · simp only [scan,guard,back,present,flag,ite_true,Option.any_none,Bool.not_false,Bool.false_and,Bool.false_eq_true,ite_false]
            rfl
          · refine ⟨by simp,rfl,?_⟩
            intro query member
            rw [pushed,Array.toList_append] at member
            rcases List.mem_append.mp member with old | new
            · exact good.2.2 query ((List.dropLast_subset stack.toList (by simpa only [Array.toList_pop] using old)))
            · exact children index node supported present query new
          · dsimp only [measure]
            omega
    · exact .inl ⟨(none,stack,steps,none),by simp only [scan,guard,Bool.false_eq_true,ite_false],by exact ⟨by simp,rfl,good.2.2⟩⟩
  have initial : property (none,#[anchor],0,none) := by simp [property,rooted]
  have final := GeneralBorrowLoop.invariant scan measure property step (none,#[anchor],0,none) initial
  cases returned : (Lean.Loop.forIn {} (none,#[anchor],0,none) scan).1 with
  | none => simpa only [returned] using final.2.1
  | some result => simpa only [returned] using final.1 result returned

end DuplicatePrefix.GeneralBorrowExposedKnownRootMinimum
