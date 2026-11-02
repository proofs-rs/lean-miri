import duplicate_prefix.GeneralBorrowCanonicalRetagQueryFrame
import duplicate_prefix.TypedRetagEntry
namespace DuplicatePrefix.GeneralBorrowCanonicalInsidePermissionFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows Miri.DataStructures
open GeneralBorrowCanonicalRetagQueryFrame TypedRetagEntry
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
/-- The actual TypedRetag inside-permission selector under the fixed precise-
interior-off configuration retains the WHOLE initial state on success and error.
No freeze/layout/query/permission-construction success is assumed. -/
theorem preserves (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (preciseOff : options.retag.preciseInteriorMut = false)
    (budget : Nat) (place : MPlaceTy Provenance) (size : Size) (policy : RetagPolicy.NewPermission) :
    ReadOnly (typed_inside (PreparedContracts.actualConfig options () remaining span).retag budget place size policy) := by
  obtain ⟨_,_,_,_,_,freeze,_,_,_,_⟩ := canonical_queries options remaining span
  obtain ⟨pointers,table,globals,choice,construction,_⟩ :=
    (CanonicalConfigFacts.actual_fields options () remaining span).retagConstruction
  have precise : (PreparedContracts.actualConfig options () remaining span).retag.preciseInteriorMut = pure false := by
    rw [construction]
    simp only [EvalRetagMachine.hooks,CompilerRetagOptions.make,preciseOff]
  unfold_typed ".TypedRetag.insidePermissions"
  rw [precise]
  simp only [pure_bind,Bool.not_false,↓reduceIte]
  apply bind_readonly
  · exact freeze place.layout.ty
  · intro frozen
    unfold_typed ".TypedRetag.checked"
    cases result : RetagPolicy.initialLocationState policy frozen <;> intro state <;> rfl
end
end DuplicatePrefix.GeneralBorrowCanonicalInsidePermissionFrame
