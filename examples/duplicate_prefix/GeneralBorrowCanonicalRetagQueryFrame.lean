import duplicate_prefix.CanonicalConfigFacts
namespace DuplicatePrefix.GeneralBorrowCanonicalRetagQueryFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
/-- The retained state on success AND error; no query success is assumed. -/
def retained {E S A : Type} (result : EStateM.Result E S A) : S :=
  match result with | .ok _ state => state | .error _ state => state
/-- Whole-state frame for a concrete effectful leaf. This is a proof property,
not a definition or additional condition of valid mutable references. -/
def ReadOnly {E S A : Type} (action : EStateM E S A) : Prop :=
  ∀ state, retained (action state) = state

theorem pure_readonly {E S A : Type} (value : A) : ReadOnly (pure value : EStateM E S A) := by
  intro state
  rfl

theorem bind_readonly {E S A B : Type} (first : EStateM E S A) (next : A → EStateM E S B)
    (before : ReadOnly first) (after : ∀ value, ReadOnly (next value)) :
    ReadOnly (first >>= next) := by
  intro state
  have same := before state
  cases firstResult : first state with
  | ok value changed =>
    have equal : changed=state := by simpa only [firstResult,retained] using same
    simp only [bind,EStateM.bind,firstResult]
    exact (after value changed).trans equal
  | error error changed =>
    simpa only [bind,EStateM.bind,firstResult,retained] using same

theorem current_frame_readonly {K U : Type} : ReadOnly (MachineHooks.currentFrame : MachineHooks.M K U _) := by
  intro state
  unfold MachineHooks.currentFrame
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind]
  cases state.stack.currentFrame? <;> rfl

/-- Actual canonical compiler retag leaves. The exact builder identities are
used; arbitrary TypedRetag dictionaries are NOT treated as state preserving. -/
theorem canonical_queries (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    let hooks := (PreparedContracts.actualConfig options () remaining span).retag
    (∀ ty, ReadOnly (hooks.typeShape ty)) ∧
    (∀ ty, ReadOnly (hooks.builtinDeref ty)) ∧
    (∀ ty, ReadOnly (hooks.referencePointee ty)) ∧
    (∀ ty, ReadOnly (hooks.isUnpin ty)) ∧
    (∀ ty, ReadOnly (hooks.isUnsafeUnpin ty)) ∧
    (∀ ty, ReadOnly (hooks.typeIsFreeze ty)) ∧
    ReadOnly hooks.preciseInteriorMut ∧ ReadOnly hooks.implicitWrites ∧
    (∀ id, ReadOnly (hooks.rustcNoWritable id)) ∧
    (∀ place size policy tag location, ReadOnly (hooks.logCreation place size policy tag location)) := by
  obtain ⟨pointers,table,globals,choice,construction,_⟩ :=
    (CanonicalConfigFacts.actual_fields options () remaining span).retagConstruction
  dsimp only
  rw [construction]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro ty state
    cases result : CompilerFacts.retagTypeShape PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context ty <;> simp only [EvalRetagMachine.hooks,CompilerRetagOptions.make,result] <;> rfl
  · intro ty state
    cases result : CompilerFacts.requiredType PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context ty "builtin_deref_explicit" <;> simp only [EvalRetagMachine.hooks,CompilerRetagOptions.make,result] <;> rfl
  · intro ty state
    cases result : CompilerFacts.referencePointee PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context ty <;> simp only [EvalRetagMachine.hooks,CompilerRetagOptions.make,result] <;> rfl
  · intro ty state
    cases result : CompilerFacts.boolean PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context ty "is_unpin" <;> simp only [EvalRetagMachine.hooks,CompilerRetagOptions.make,result] <;> rfl
  · intro ty state
    cases result : CompilerFacts.boolean PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context ty "is_unsafe_unpin" <;> simp only [EvalRetagMachine.hooks,CompilerRetagOptions.make,result] <;> rfl
  · intro ty state
    cases result : CompilerFacts.boolean PreparedReflection.actual.compiler.lifecycle.calls.symbols.facts.context ty "is_freeze" <;> simp only [EvalRetagMachine.hooks,CompilerRetagOptions.make,result] <;> rfl
  · exact pure_readonly _
  · exact pure_readonly _
  · intro id state
    cases result : CompilerRetagOptions.rustcNoWritable PreparedReflection.actual.compiler id <;> simp only [EvalRetagMachine.hooks,CompilerRetagOptions.make,result] <;> rfl
  · intro place size policy tag location
    exact pure_readonly _
end
end DuplicatePrefix.GeneralBorrowCanonicalRetagQueryFrame
