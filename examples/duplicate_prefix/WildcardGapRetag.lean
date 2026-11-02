import duplicate_prefix.WildcardGapResolver
import duplicate_prefix.TypedRetagEmpty
namespace DuplicatePrefix.WildcardGapRetag
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedRetagEmpty
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- An unresolved wildcard takes the actual no-location retag branch. -/
theorem canonical_zero_reborrow {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared) (options : CompilerRetagOptions.Options)
    (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (budget : Nat) (place : MPlaceTy Provenance) (tag : BorTag)
    (state : ValidityMachine.State K U) (address : UInt64)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes address))
    (mode : state.machine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardGapResolver.Miss state.machine.user.addresses state.machine.memory address) :
    TypedRetag.reborrow (EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler options) access projection vtable pointers choice)
      budget place Size.ZERO ChildBorrow.fnEntryPolicy tag state = .ok (some .wildcard) state := by
  have check := RetagPointerChecks.check_pointer_zero access place.mplace.ptr state
  have resolve : TypedValidityProviders.resolveAllocation pointers place.mplace.ptr state = .ok none state := by
    rw [pointer]
    exact WildcardGapResolver.resolve_miss pointers state address mode miss
  unfold TypedRetag.reborrow
  simp only [EvalRetagMachine.hooks, CompilerRetagOptions.make, check, resolve,
    bind, EStateM.bind, pure, EStateM.pure]
  simp [Size.ZERO, pointer, Pointer.new, bind, EStateM.bind, pure, EStateM.pure]

private theorem zero_retag_place_stage {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : state.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (wildcard : place.mplace.ptr.provenance = some .wildcard)
    (size : h.sizeAndAlign place = pure (some (Size.ZERO, Align.ONE)))
    (reborrow : TypedRetag.reborrow h budget place Size.ZERO ChildBorrow.fnEntryPolicy
      tracker.global.nextPointerTag (afterTag state tracker fresh) =
      .ok (some .wildcard) (afterTag state tracker fresh)) :
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
  simp only [wildcard, bind, EStateM.bind, pure, EStateM.pure]
  simp only [← wildcard]

theorem canonical_zero_retag_place {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (budget : Nat) (place : MPlaceTy Provenance) (state : ValidityMachine.State K U)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (address : UInt64)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes address))
    (mode : state.machine.user.addresses.provenanceMode ≠ .strict)
    (miss : WildcardGapResolver.Miss state.machine.user.addresses state.machine.memory address)
    (slice : TypedRetagEntry.SliceFacts projection choice place 0) :
    TypedRetag.retagPlace (EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice)
      budget place ChildBorrow.fnEntryPolicy state = .ok place (afterTag state tracker fresh) := by
  exact zero_retag_place_stage _ budget place state tracker enabled fresh (by rw [pointer];rfl)
    (TypedRetagEntry.canonical_size prepared runtime compiler access projection vtable pointers choice
      place 0 slice)
    (canonical_zero_reborrow prepared runtime compiler ⟨false, false⟩ access projection vtable pointers choice
      budget place tracker.global.nextPointerTag (afterTag state tracker fresh) address pointer mode miss)


end DuplicatePrefix.WildcardGapRetag
