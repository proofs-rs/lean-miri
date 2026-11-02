import duplicate_prefix.GeneralBorrowCanonicalRetagQueryFrame
import duplicate_prefix.RetagPointerChecks
namespace DuplicatePrefix.GeneralBorrowCanonicalPointerCausalFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open GeneralBorrowCanonicalRetagQueryFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
/-- Actual address resolution inspects metadata only; all successful and failed
lookup outcomes retain the exact input state. Hooks contribute arithmetic and
pure error classification, never arbitrary stateful effects in this function. -/
theorem address_resolution_state {K U : Type} (pointers : PointerMachine.Hooks K U)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (state : PointerMachine.State K U) (pointer : Pointer (Option Provenance)) (size : Int) :
    (PointerMachine.resolvePointer pointers memory state pointer size).state = state := by
  unfold PointerMachine.resolvePointer
  simp only [Id.run,bind,pure]
  repeat' first | rfl | split

theorem resolve_allocation_readonly {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (pointer : Pointer (Option Provenance)) :
    ReadOnly (TypedValidityProviders.resolveAllocation pointers pointer) := by
  intro state
  have convert (result : MachineHookResult (ValidityMachine.State K U)
      (Except UInt64 (ResolvedPointer Provenance))) (same : result.state=state) :
      retained ((do
        set result.state
        match result.outcome with
        | .error error => throw (.callback error)
        | .ok (.error _) => pure none
        | .ok (.ok resolved) =>
          let extra := match resolved.extra with
            | .concrete _ tag => ProvenanceExtra.concrete tag
            | .wildcard => ProvenanceExtra.wildcard
          pure (some (⟨resolved.allocId,resolved.offset,extra⟩ : Miri.TreeBorrows.RetagPipeline.ResolvedLocation))
        : ValidityMachine.M K U _) state) = state := by
    cases result with
    | mk changed outcome =>
      dsimp only at same
      subst changed
      cases outcome with
      | error error => rfl
      | ok resolved => cases resolved <;> rfl
  exact convert (PointerMachine.resolvePointer pointers state.machine.memory state pointer 0)
    (address_resolution_state pointers state.machine.memory state pointer 0)

/-- The canonical typed-memory resolver has a separate MachineState monad.
It likewise retains that state on every metadata/address/error path. -/
theorem memory_resolution_readonly {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (pointer : Pointer (Option Provenance)) (size : Int) :
    ReadOnly (TypedMemoryProviders.resolvePointer pointers memory pointer size) := by
  intro state
  unfold TypedMemoryProviders.resolvePointer
  by_cases bad : (decide (size < -(2^63 : Int)) || decide (size ≥ 2^63)) = true
  · simp only [bad,↓reduceIte]
    rfl
  · simp only [bad,Bool.false_eq_true,↓reduceIte]
    cases provenance : pointer.provenance with
    | none => simp only [provenance];rfl
    | some extra =>
      simp only [provenance,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
      cases located : state.user.addresses.ptrGetAlloc (Pointer.new extra pointer.offset) (Int64.ofInt size)
        {sizeOf:=fun id => (memory.getAllocInfo id).toOption.map (·.size),isLive:=fun id => some (memory.isAllocLive id)} pointers.arithmetic with
      | error error => simp only [located];rfl
      | ok allocation =>
        cases allocation with
        | none => simp only [located];rfl
        | some allocation => simp only [located];rfl

private theorem throw_readonly {E S A : Type} (error : E) : ReadOnly (throw error : EStateM E S A) := by
  intro state
  rfl
private theorem get_readonly {E S : Type} : ReadOnly (get : EStateM E S S) := by
  intro state
  rfl
private theorem if_readonly {E S A : Type} (condition : Prop) [Decidable condition]
    (yes no : EStateM E S A) (first : ReadOnly yes) (second : ReadOnly no) :
    ReadOnly (if condition then yes else no) := by
  by_cases branch : condition
  · simpa only [branch,↓reduceIte] using first
  · simpa only [branch,↓reduceIte] using second

theorem validity_resolution_readonly {K U : Type} (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (pointer : Pointer (Option Provenance)) (size : Int) :
    ReadOnly (retag_validity_resolve access pointer size) := by
  intro state
  have same := memory_resolution_readonly pointers state.machine.memory pointer size state.machine
  unfold_internal ".ValidityMachine.resolve"
  rw [wiring]
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,set,EStateM.set,pure,EStateM.pure]
  generalize resolved : TypedMemoryProviders.resolvePointer pointers state.machine.memory pointer size state.machine = result
  rw [resolved] at same
  cases result with
  | ok value machine =>
    dsimp only [retained] at same
    subst machine
    rfl
  | error error machine =>
    dsimp only [retained] at same
    subst machine
    rfl

theorem check_result_readonly {K U : Type} (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (pointer : Pointer (Option Provenance)) (size : Size) :
    ReadOnly (ValidityMachine.checkPointerAccessResult access pointer size) := by
  have finish (outcome : Except AccessError Unit) :
      ReadOnly (match outcome with
        | .ok () => (pure (.ok ()) : ValidityMachine.M K U (Except AccessError Unit))
        | .error error => pure (.error error)) := by
    cases outcome with
    | ok unit => cases unit; exact pure_readonly _
    | error error => exact pure_readonly _
  unfold ValidityMachine.checkPointerAccessResult
  cases converted : sizeAsI64 size with
  | error error => simp only [converted];exact pure_readonly _
  | ok signed =>
    simp only [converted]
    repeat' first
      | exact pure_readonly _
      | exact validity_resolution_readonly access pointers wiring pointer _
      | exact finish _
      | exact get_readonly
      | apply if_readonly
      | apply bind_readonly
      | intro argument
      | (split <;> exact pure_readonly _)
      | (split <;> rfl)

/-- Source-wiring premise only: no pointer-validity or operation-success premise
is used. Actual checkPtrAccess returns its real errors and retains the state. -/
theorem check_pointer_readonly {K U : Type} (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (pointer : Pointer (Option Provenance)) (size : Size) :
    ReadOnly (ValidityMachine.checkPointerAccess access pointer size) := by
  unfold ValidityMachine.checkPointerAccess
  apply bind_readonly _ _ (check_result_readonly access pointers wiring pointer size)
  intro result
  cases result
  · exact throw_readonly _
  · exact pure_readonly _

/-- These are the ACTUAL fixed configuration's retag pointer leaves. No live,
cache, width, nonnull, access success or additional safety premise is assumed. -/
theorem canonical (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) :
    let hooks := (PreparedContracts.actualConfig options () remaining span).retag
    (∀ pointer, ReadOnly (hooks.resolveAllocation pointer)) ∧
    (∀ pointer size, ReadOnly (hooks.checkPtrAccess pointer size)) := by
  obtain ⟨pointers,table,globals,choice,construction,arithmetic,wiring,ensure,synchronize⟩ :=
    (CanonicalConfigFacts.actual_fields options () remaining span).retagConstruction
  dsimp only
  rw [construction]
  constructor
  · intro pointer
    exact resolve_allocation_readonly pointers pointer
  · intro pointer size
    exact check_pointer_readonly _ pointers wiring pointer size
end
end DuplicatePrefix.GeneralBorrowCanonicalPointerCausalFrame
