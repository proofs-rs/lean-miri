import Miri.Input.SourceCompilerTypes
import Init.Data.Range.Lemmas

/-! Successful physical interning preserves existing canonical type and layout
rows. These are local transition properties, with no global World invariant. -/
namespace Miri.Input.SourceCompilerWorld
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

theorem internType_pools (before after : World) (shape : TypeShape) (layout : Layout) (display : String) (id : TypeId)
    (result : internType before shape layout display = .ok (after,id)) :
    (after.canonical.types = before.canonical.types ∧ after.canonical.layouts = before.canonical.layouts) ∨
    (∃ node, after.canonical.types = before.canonical.types.push node ∧
      after.canonical.layouts = before.canonical.layouts.push layout) := by
  simp only [internType, bind, Except.bind, pure, Except.pure] at result
  repeat' split at result
  all_goals simp_all only [reduceCtorEq, Except.ok.injEq, Prod.mk.injEq]
  all_goals rcases result with ⟨rfl, rfl⟩
  all_goals first | exact Or.inr ⟨_,rfl,rfl⟩ | exact Or.inl ⟨True.intro,True.intro⟩


theorem internType_preserves_rows (before after : World) (shape : TypeShape)
    (layout : Layout) (display : String) (id : TypeId)
    (result : internType before shape layout display = .ok (after,id)) :
    (∀ (i : Nat) (node : TypeNode), before.canonical.types[i]? = some node → after.canonical.types[i]? = some node) ∧
    (∀ (i : Nat) (row : Layout), before.canonical.layouts[i]? = some row → after.canonical.layouts[i]? = some row) := by
  rcases internType_pools before after shape layout display id result with unchanged | ⟨node,types,layouts⟩
  · rcases unchanged with ⟨types,layouts⟩
    simp only [types,layouts]
    exact ⟨fun _ _ h => h, fun _ _ h => h⟩
  · constructor
    · intro i old present
      rw [types]
      rcases Array.getElem?_eq_some_iff.mp present with ⟨bound,row⟩
      exact (Array.getElem?_push_lt bound).trans (congrArg some row)
    · intro i old present
      rw [layouts]
      rcases Array.getElem?_eq_some_iff.mp present with ⟨bound,row⟩
      exact (Array.getElem?_push_lt bound).trans (congrArg some row)


theorem internDefinition_preserves_physical_pools (before after : World) (raw : DefinitionId) (id : Nat)
    (result : internDefinition before raw = .ok (after,id)) :
    after.canonical.types = before.canonical.types ∧
      after.canonical.layouts = before.canonical.layouts := by
  simp only [internDefinition, bind, Except.bind, pure, Except.pure] at result
  repeat' split at result
  all_goals simp_all only [reduceCtorEq, Except.ok.injEq, Prod.mk.injEq]
  all_goals rcases result with ⟨rfl, rfl⟩
  all_goals simp


theorem internScalarConstant_preserves_physical_pools (before after : World) (typeId bits sizeBytes : Nat) (id : Nat)
    (result : internScalarConstant before typeId bits sizeBytes = .ok (after,id)) :
    after.canonical.types = before.canonical.types ∧
      after.canonical.layouts = before.canonical.layouts := by
  simp only [internScalarConstant, bind, Except.bind, pure, Except.pure] at result
  repeat' split at result
  all_goals simp_all only [reduceCtorEq, Except.ok.injEq, Prod.mk.injEq]
  all_goals rcases result with ⟨rfl, rfl⟩
  all_goals simp


theorem internPredicate_preserves_physical_pools (before after : World) (predicate : VtablePredicate) (id : Nat)
    (result : internPredicate before predicate = .ok (after,id)) :
    after.canonical.types = before.canonical.types ∧
      after.canonical.layouts = before.canonical.layouts := by
  simp only [internPredicate, bind, Except.bind, pure, Except.pure] at result
  repeat' split at result
  all_goals simp_all only [reduceCtorEq, Except.ok.injEq, Prod.mk.injEq]
  all_goals rcases result with ⟨rfl, rfl⟩
  all_goals simp

/-- World seeding validates and indexes the input without replacing its canonical
rows. The loop invariant concerns only this construction, not arbitrary Worlds. -/
theorem create_canonical (input : ImportDocument) (world : World) (result : create input = .ok world) : world.canonical = input := by
  have loop_canonical (xs : List Nat)
      (step : Nat → World → Except String (ForInStep World))
      (preserves : ∀ i before next, step i before = .ok next →
        (match next with | .done w | .yield w => w.canonical) = before.canonical)
      (before after : World) (result : forIn xs before step = .ok after) :
      after.canonical = before.canonical := by
    induction xs generalizing before with
    | nil =>
      simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at result
      subst after
      rfl
    | cons i xs ih =>
      simp only [List.forIn_cons, bind, Except.bind] at result
      split at result
      · contradiction
      · rename_i next stepResult
        cases next with
        | done w =>
          simp only [pure, Except.pure, Except.ok.injEq] at result
          subst after
          exact preserves i before (.done w) stepResult
        | yield w =>
          exact (ih w result).trans (preserves i before (.yield w) stepResult)
  simp only [create, bind, Except.bind, pure, Except.pure] at result
  repeat' split at result
  all_goals simp_all only [reduceCtorEq, Except.ok.injEq]
  all_goals subst world
  all_goals
    simp only [Std.Legacy.Range.forIn_eq_forIn_range'] at *
    refine loop_canonical _ _ ?_ {canonical := input} _ (by assumption)
    intro i before next success
    try simp only [bind, Except.bind, pure, Except.pure] at success
    repeat' split at success
    all_goals simp_all only [reduceCtorEq, Except.ok.injEq]
    all_goals cases success
    all_goals rfl

end Miri.Input.SourceCompilerWorld
