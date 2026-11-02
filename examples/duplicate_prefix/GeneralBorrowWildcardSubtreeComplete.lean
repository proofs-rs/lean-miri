import duplicate_prefix.GeneralBorrowWildcardSubtreeInvariant

namespace DuplicatePrefix.GeneralBorrowWildcardSubtreeComplete
open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.TreeBorrows.Tree
open GeneralBorrowWildcardVirtualLeaf (effective)
open GeneralBorrowWildcardSubtreeData GeneralBorrowWildcardSubtreeStack GeneralBorrowWildcardSubtreeState
open GeneralBorrowWildcardSubtreeInvariant
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

/-- Full actual virtual-root DFS for any unexposed foreign-owned supported
subtree with zero kind counters. Raw graph weights discharge the original
source's exact step bound; they do not assume traversal/access success. -/
theorem access (tree : BorrowTree) (initial : LocationTree) (root : UniIndex)
    (maximum : Option BorTag) (kind : AccessKind) (protections : ProtectedTags)
    (weights : Weights tree) (rootBound : weights.weight root ≤ tree.nodes.size)
    (data : Data tree initial root kind protections) :
    let result := tree.performWildcardAccessAt initial root maximum kind protections true
    result.status = .Completed ∧ Owned data result.location ∧
      result.location.exposedCache = initial.exposedCache ∧
      (∀ query, ¬data.support query → result.location.perms.get query = initial.perms.get query) := by
  unfold BorrowTree.performWildcardAccessAt
  simp only [Id.run,bind,pure,ForIn.forIn]
  name_range_scan
  have step : ∀ state, Invariant weights data state →
      (∃ final, scan () state = .done final ∧ Invariant weights data final) ∨
      ∃ next, scan () state = .yield next ∧ Invariant weights data next ∧
        potential weights.weight next.2.2.2.1 < potential weights.weight state.2.2.2.1 := by
    intro state valid
    rcases state with ⟨location,witness,status,stack,steps⟩
    have witnessEq := valid.witness
    have statusEq := valid.status
    dsimp only at witnessEq statusEq
    subst witness
    subst status
    by_cases empty : stack = #[]
    · subst stack
      exact .inl ⟨_,by simp [scan],valid⟩
    · obtain ⟨baseStack,⟨index,afterChildren⟩,rfl⟩ := Array.exists_push_of_ne_empty empty
      have supported : data.support index := valid.known (index,afterChildren) (by simp)
      obtain ⟨node,present⟩ := data.present index supported
      have notPast : ¬steps+1 > tree.nodes.size*2+1 := by
        have bound := valid.budget
        dsimp only at bound
        omega
      have zero : GeneralBorrowWildcardRelatednessBounds.count location.exposedCache index kind = 0 := by
        rw [valid.cache]
        exact data.zero index supported
      have related : ∀ clamp, location.exposedCache.accessRelatedness root index kind true clamp = some .ForeignAccess :=
        fun clamp => GeneralBorrowWildcardRelatednessBounds.zero_classify location.exposedCache root index kind clamp zero
      cases afterChildren with
      | false =>
        have positive : 1 ≤ weights.weight index := by
          have bound := weights.children index node present
          omega
        cases skipped : (effective location index node).skipIfKnownNoop kind .ForeignAccess with
        | SkipSelfAndChildren =>
          dsimp only [effective] at skipped
          refine .inr ⟨(location,false,.Completed,baseStack,steps+1),?_,?_,?_⟩
          · simp only [scan]
            unfold_leaf_helpers
            simp [notPast,present,related,skipped,effective,Id.run,bind,pure]
            try unfold_leaf_helpers
            try simp [related,skipped,effective]
          · exact pop weights data location baseStack (index,false) steps valid (by simp [cost];omega)
          · rw [potential_push]
            simp only [cost,Bool.false_eq_true,↓reduceIte]
            omega
        | Recurse =>
          dsimp only [effective] at skipped
          have pushing := children_loop node.children (baseStack.push (index,true))
          simp only [forIn'_eq_forIn,pure] at pushing
          refine .inr ⟨(location,false,.Completed,expanded baseStack index node.children,steps+1),?_,?_,?_⟩
          · simp only [scan]
            unfold_leaf_helpers
            simp [notPast,present,related,skipped,effective,Id.run,bind,pure]
            try unfold_leaf_helpers
            simp [related,skipped,effective,pushing,expanded]
          · exact expand weights data location baseStack index node steps valid present skipped
          · rw [expanded_potential,potential_push]
            simp only [cost,Bool.false_eq_true,↓reduceIte]
            have bounded := weights.children index node present
            omega
      | true =>
        have recurse := valid.pending index node (by simp) present
        obtain skipped | ⟨recorded,next,transition,record,access,preserved⟩ :=
          GeneralBorrowPermissions.visit_success (effective location index node) .ForeignAccess
            (protections.contains node.tag) kind (valid.owned index node supported present)
        · rw [recurse] at skipped
          cases skipped
        · have unexposed := data.unexposed index node supported present
          refine .inr ⟨(write location index node recorded next,false,.Completed,baseStack,steps+1),?_,?_,?_⟩
          · simp only [scan]
            unfold_leaf_helpers
            simp [notPast,present,related,unexposed,Id.run,bind,pure]
            try unfold_leaf_helpers
            simp only [related,or_insert_snd,record,access,LocationState.AccessResult.resultingState,
              recurse,reduceCtorEq,and_false,ite_false]
            rfl
          · exact post weights data location baseStack index node steps recorded next valid present preserved
          · rw [potential_push]
            simp [cost]
  have retained := GeneralBorrowLoop.invariant scan
    (fun state : LoopState => potential weights.weight state.2.2.2.1)
    (Invariant weights data) step (initial,false,.Completed,#[(root,false)],0)
    (GeneralBorrowWildcardSubtreeInvariant.initial weights data)
  simp only [Bool.not_true,Bool.and_false,Bool.false_eq_true,↓reduceIte]
  exact ⟨retained.status,retained.owned,retained.cache,retained.outside⟩

end DuplicatePrefix.GeneralBorrowWildcardSubtreeComplete
