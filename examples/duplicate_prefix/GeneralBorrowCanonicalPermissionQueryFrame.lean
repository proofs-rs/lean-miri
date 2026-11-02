import duplicate_prefix.GeneralBorrowCanonicalRetagQueryFrame
namespace DuplicatePrefix.GeneralBorrowCanonicalPermissionQueryFrame
open Miri Miri.Input Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open GeneralBorrowCanonicalRetagQueryFrame
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
noncomputable section
private theorem ite_readonly {E S A : Type} (condition : Prop) [Decidable condition]
    (yes no : EStateM E S A) (first : ReadOnly yes) (second : ReadOnly no) :
    ReadOnly (if condition then yes else no) := by
  by_cases branch : condition
  · simpa only [branch,↓reduceIte] using first
  · simpa only [branch,↓reduceIte] using second

private theorem permission_readonly {K U : Type} (hooks : TypedRetag.Hooks K U)
    (unpin : ∀ ty, ReadOnly (hooks.isUnpin ty))
    (unsafeUnpin : ∀ ty, ReadOnly (hooks.isUnsafeUnpin ty))
    (freeze : ∀ ty, ReadOnly (hooks.typeIsFreeze ty))
    (implicitWrites : ReadOnly hooks.implicitWrites)
    (noWritable : ∀ id, ReadOnly (hooks.rustcNoWritable id))
    (pointee : TyId) (kind : RetagPolicy.ReferenceKind) (mode : RetagPolicy.RetagMode) :
    ReadOnly (TypedRetag.newPermission hooks pointee kind mode) := by
  unfold TypedRetag.newPermission
  repeat' first
    | exact pure_readonly _
    | exact unpin _
    | exact unsafeUnpin _
    | exact freeze _
    | exact implicitWrites
    | exact noWritable _
    | exact current_frame_readonly
    | apply ite_readonly
    | apply bind_readonly
    | intro

/-- The actual fixed-configuration permission selector retains its entire
initial state on both success and error. Compiler queries, configuration flags
and current-frame lookup are proved read-only from their real definitions. -/
theorem preserves (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery) (pointee : TyId)
    (kind : RetagPolicy.ReferenceKind) (mode : RetagPolicy.RetagMode) :
    ReadOnly (TypedRetag.newPermission (PreparedContracts.actualConfig options () remaining span).retag pointee kind mode) := by
  obtain ⟨_,_,_,unpin,unsafeUnpin,freeze,_,implicitWrites,noWritable,_⟩ := canonical_queries options remaining span
  exact permission_readonly _ unpin unsafeUnpin freeze implicitWrites noWritable pointee kind mode

end
end DuplicatePrefix.GeneralBorrowCanonicalPermissionQueryFrame
