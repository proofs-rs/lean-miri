import duplicate_prefix.TypedRetagEntry

/-! The no-provenance, zero-length slice path of the actual typed retag driver. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
namespace DuplicatePrefix.TypedRetagEmpty
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter

private theorem increment_nonzero (tag : BorTag)
    (fresh : tag.value < 18446744073709551615) : tag.value + 1 ≠ 0 := by
  have bound : tag.value.toNat < 18446744073709551615 := by
    simpa [UInt64.lt_iff_toNat_lt] using fresh
  have fits : tag.value.toNat + 1 < 2 ^ 64 := by omega
  intro zero
  have equality := congrArg UInt64.toNat zero
  simp only [UInt64.toNat_add, UInt64.toNat_one, UInt64.toNat_zero,
    Nat.mod_eq_of_lt fits] at equality
  omega

def successorTag (tag : BorTag) (fresh : tag.value < 18446744073709551615) : BorTag :=
  ⟨tag.value + 1, increment_nonzero tag fresh⟩

theorem allocate_tag (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615) :
    global.newPointerTag = .ok
      ({global with nextPointerTag := successorTag global.nextPointerTag fresh}, global.nextPointerTag) := by
  have notMax : global.nextPointerTag.value ≠ 18446744073709551615 := by
    intro equality
    rw [equality] at fresh
    exact (UInt64.lt_irrefl _) fresh
  simp [GlobalState.newPointerTag, BorTag.succ, BorTag.ofUInt64, notMax,
    increment_nonzero global.nextPointerTag fresh, successorTag]

def afterTag {K U : Type} (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615) : MachineHooks.State K U :=
  let global := {tracker.global with nextPointerTag := successorTag tracker.global.nextPointerTag fresh}
  {state with machine := {state.machine with borrowTracker := some {tracker with global}}}

theorem canonical_zero_reborrow {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared) (options : CompilerRetagOptions.Options)
    (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (budget : Nat) (place : MPlaceTy Provenance) (tag : BorTag)
    (state : ValidityMachine.State K U) (noProvenance : place.mplace.ptr.provenance = none) :
    TypedRetag.reborrow (EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler options) access projection vtable pointers choice)
      budget place Size.ZERO ChildBorrow.fnEntryPolicy tag state = .ok none state := by
  have check := RetagPointerChecks.check_pointer_zero access place.mplace.ptr state
  have resolve := RetagPointerChecks.resolve_allocation_none pointers place.mplace.ptr state noProvenance
  unfold TypedRetag.reborrow
  simp only [EvalRetagMachine.hooks, CompilerRetagOptions.make, check, resolve,
    bind, EStateM.bind, pure, EStateM.pure]
  simp [Size.ZERO, noProvenance, bind, EStateM.bind, pure, EStateM.pure]

#print axioms canonical_zero_reborrow

private theorem zero_retag_place_stage {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : state.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (noProvenance : place.mplace.ptr.provenance = none)
    (size : h.sizeAndAlign place = pure (some (Size.ZERO, Align.ONE)))
    (reborrow : TypedRetag.reborrow h budget place Size.ZERO ChildBorrow.fnEntryPolicy
      tracker.global.nextPointerTag (afterTag state tracker fresh) =
      .ok none (afterTag state tracker fresh)) :
    TypedRetag.retagPlace h budget place ChildBorrow.fnEntryPolicy state =
      .ok place (afterTag state tracker fresh) := by
  unfold TypedRetag.retagPlace
  simp only [size, bind, EStateM.bind, pure, EStateM.pure, Option.map_some, Option.getD_some]
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, enabled, allocate_tag tracker.global fresh]
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure]
  erw [reborrow]
  simp only [noProvenance, bind, EStateM.bind, pure, EStateM.pure]
  simp only [← noProvenance]

theorem canonical_zero_retag_place {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (budget : Nat) (place : MPlaceTy Provenance) (state : ValidityMachine.State K U)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (noProvenance : place.mplace.ptr.provenance = none)
    (slice : TypedRetagEntry.SliceFacts projection choice place 0) :
    TypedRetag.retagPlace (EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice)
      budget place ChildBorrow.fnEntryPolicy state = .ok place (afterTag state tracker fresh) := by
  exact zero_retag_place_stage _ budget place state tracker enabled fresh noProvenance
    (TypedRetagEntry.canonical_size prepared runtime compiler access projection vtable pointers choice
      place 0 slice)
    (canonical_zero_reborrow prepared runtime compiler ⟨false, false⟩ access projection vtable pointers choice
      budget place tracker.global.nextPointerTag (afterTag state tracker fresh) noProvenance)

#print axioms canonical_zero_retag_place

private theorem zero_pointer_stage {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (value : RvalueImmTy Provenance)
    (place : MPlaceTy Provenance) (pointee : TyId) (before after : MachineHooks.State K U)
    (shape : h.typeShape value.layout.ty = pure .reference)
    (pointeeQuery : h.referencePointee value.layout.ty = pure (pointee, .Mut))
    (policy : TypedRetag.newPermission h pointee .Mutable .FnEntry before =
      .ok (some ChildBorrow.fnEntryPolicy) before)
    (construct : h.immPtrToMPlace value = pure place)
    (retag : TypedRetag.retagPlace h budget place ChildBorrow.fnEntryPolicy before = .ok place after)
    (reconstruct : h.reconstruct value place = pure value) :
    TypedRetag.retagPtrValue h budget value value.layout.ty .FnEntry before =
      .ok (some value) after := by
  unfold TypedRetag.retagPtrValue
  simp only [shape, pointeeQuery, RetagPipeline.RetagTypeShape.reference,
    RetagPipeline.RetagTypeShape.classify, Bool.false_eq_true, ↓reduceIte,
    bind, EStateM.bind, pure, EStateM.pure]
  have mutable : (Miri.MIR.Mutability.Mut == .Mut) = true := rfl
  simp only [mutable, ↓reduceIte, policy, construct, retag, reconstruct,
    bind, EStateM.bind, pure, EStateM.pure]

theorem canonical_zero_retag_pointer {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C) (budget : Nat)
    (state : ValidityMachine.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (frameShape : state.stack.frames = frames.push frame)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (reference pointee : LocalLayout) (address : UInt64)
    (width : access.runtime.base.pointerWidth = .w64)
    (slice : TypedRetagEntry.SliceFacts projection choice
      (RetagReferencePlace.integerSlicePlace address 0 pointee) 0)
    (referenceShape : CompilerFacts.retagTypeShape prepared.context reference.ty = .ok .reference)
    (referencePointee : CompilerFacts.referencePointee prepared.context reference.ty = .ok (pointee.ty, .Mut))
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some pointee.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context pointee.ty = .ok pointee)
    (pointeeAlign : pointee.layout.align.abi = Align.ONE)
    (unpin : CompilerFacts.boolean prepared.context pointee.ty "is_unpin" = .ok true)
    (unsafeUnpin : CompilerFacts.boolean prepared.context pointee.ty "is_unsafe_unpin" = .ok true)
    (frozen : CompilerFacts.boolean prepared.context pointee.ty "is_freeze" = .ok true) :
    let h := EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
    TypedRetag.retagPtrValue h budget (RetagReferencePlace.integerSliceValue address 0 reference)
      reference.ty .FnEntry state =
      .ok (some (RetagReferencePlace.integerSliceValue address 0 reference)) (afterTag state tracker fresh) := by
  let h := EvalRetagMachine.hooks prepared runtime
    (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
  let value := RetagReferencePlace.integerSliceValue address 0 reference
  let place := RetagReferencePlace.integerSlicePlace address 0 pointee
  have shape : h.typeShape value.layout.ty = pure .reference := by
    simp only [h, value, RetagReferencePlace.integerSliceValue, EvalRetagMachine.hooks]
    unfold_typed ".EvalRetagMachine.lift"
    rw [referenceShape]
  have pointeeQuery : h.referencePointee value.layout.ty = pure (pointee.ty, .Mut) := by
    simp only [h, value, RetagReferencePlace.integerSliceValue, EvalRetagMachine.hooks]
    unfold_typed ".EvalRetagMachine.lift"
    rw [referencePointee]
  have policy := TypedRetagEntry.canonical_new_permission prepared runtime compiler access projection vtable
    pointers choice pointee.ty state frames frame frameShape unpin unsafeUnpin frozen
  have construct : h.immPtrToMPlace value = pure place := by
    exact RetagReferencePlace.canonical_from_integer access prepared choice address 0 reference pointee
      dereference pointeeLayout pointeeAlign width
  have retag := canonical_zero_retag_place prepared runtime compiler access projection vtable pointers choice
    budget place state tracker enabled fresh rfl slice
  have reconstruct : h.reconstruct value place = pure value :=
    RetagReferencePlace.canonical_reconstruct_integer prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
      value address 0 pointee width
  exact zero_pointer_stage h budget value place pointee.ty state (afterTag state tracker fresh)
    shape pointeeQuery policy construct retag reconstruct

#print axioms canonical_zero_retag_pointer
end DuplicatePrefix.TypedRetagEmpty

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.TypedRetagEmpty.canonical_zero_retag_pointer,
      ``DuplicatePrefix.TypedRetagEmpty.canonical_zero_retag_place,
      ``DuplicatePrefix.TypedRetagEmpty.canonical_zero_reborrow,
      ``DuplicatePrefix.TypedRetagEmpty.allocate_tag] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
