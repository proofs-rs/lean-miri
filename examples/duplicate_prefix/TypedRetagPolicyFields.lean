import duplicate_prefix.TypedRetagEntry

/-! Actual policy/permission source steps from immutable query-field values. -/
namespace DuplicatePrefix.TypedRetagPolicyFields
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Interpreter

theorem new_permission {K U : Type} (h : TypedRetag.Hooks K U) (pointee : TyId)
    (state : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (shape : state.stack.frames = frames.push frame)
    (unpin : h.isUnpin pointee = pure true)
    (unsafeUnpin : h.isUnsafeUnpin pointee = pure true)
    (freeze : h.typeIsFreeze pointee = pure true)
    (implicitWrites : h.implicitWrites = pure false) :
    TypedRetag.newPermission h pointee .Mutable .FnEntry state =
      .ok (some ChildBorrow.fnEntryPolicy) state := by
  unfold TypedRetag.newPermission
  simp only [unpin, unsafeUnpin, freeze, implicitWrites, beq_iff_eq, reduceCtorEq,
    ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure, Bool.true_eq]
  rw [TypedRetagEntry.current_frame_pushed state frames frame shape]
  have policy : RetagPolicy.create ⟨true, true, true⟩ .Mutable .FnEntry ⟨false, false⟩ =
      some ChildBorrow.fnEntryPolicy := by decide
  simp only [bind, EStateM.bind, pure, EStateM.pure, Bool.false_eq_true, ↓reduceIte, policy]

theorem inside_permissions {K U : Type} (h : TypedRetag.Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size)
    (precise : h.preciseInteriorMut = pure false)
    (frozen : h.typeIsFreeze place.layout.ty = pure true) :
    typed_inside h budget place size ChildBorrow.fnEntryPolicy =
      pure (DedupRangeMap.new size ChildBorrow.fnEntryLocation) := by
  unfold_typed ".TypedRetag.insidePermissions"
  unfold_typed ".TypedRetag.checked"
  funext state
  simp [precise, frozen, ChildBorrow.mutable_fn_entry_initial_location,
    bind, EStateM.bind, pure, EStateM.pure]

theorem new_permission_general {K U : Type} (h : TypedRetag.Hooks K U) (pointee : TyId)
    (kind : RetagPolicy.ReferenceKind) (mode : RetagPolicy.RetagMode)
    (state : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (shape : state.stack.frames = frames.push frame)
    (unpin : h.isUnpin pointee = pure true)
    (unsafeUnpin : h.isUnsafeUnpin pointee = pure true)
    (freeze : h.typeIsFreeze pointee = pure true)
    (implicitWrites : h.implicitWrites = pure false) :
    TypedRetag.newPermission h pointee kind mode state =
      .ok (RetagPolicy.create ⟨true, true, true⟩ kind mode ⟨false, false⟩) state := by
  cases mode <;> unfold TypedRetag.newPermission <;>
    simp only [unpin, unsafeUnpin, freeze, implicitWrites, beq_iff_eq, reduceCtorEq,
      ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure, Bool.true_eq,
      RetagPolicy.none_mode_never_creates_permission]
  all_goals
    rw [TypedRetagEntry.current_frame_pushed state frames frame shape]

theorem inside_for_policy {K U : Type} (h : TypedRetag.Hooks K U) (budget : Nat)
    (place : MPlaceTy Provenance) (size : Size) (policy : RetagPolicy.NewPermission)
    (location : Tree.LocationState) (initial : RetagPolicy.initialLocationState policy true = .ok location)
    (precise : h.preciseInteriorMut = pure false)
    (frozen : h.typeIsFreeze place.layout.ty = pure true) :
    typed_inside h budget place size policy = pure (DedupRangeMap.new size location) := by
  unfold_typed ".TypedRetag.insidePermissions"
  unfold_typed ".TypedRetag.checked"
  funext state
  simp [precise, frozen, initial, bind, EStateM.bind, pure, EStateM.pure]

#print axioms new_permission
#print axioms inside_permissions
#print axioms new_permission_general
#print axioms inside_for_policy
end DuplicatePrefix.TypedRetagPolicyFields
