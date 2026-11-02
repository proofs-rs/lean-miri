import duplicate_prefix.CurrentCallEmptySelectedHit
import duplicate_prefix.WildcardMissRetag

/-! The query-local miss alternative reaches the actual no-location zero-byte
reborrow. This consumes no additional memory, image or cache premise. Selected
hits retain their actual target/image obligations in the existing Hit packet;
this theorem does not establish their materialization or ordinary coverage. -/
namespace DuplicatePrefix.CurrentCallEmptyMissOperation
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.MIR
open Miri.Input Miri.Interpreter Miri.TreeBorrows
open DuplicatePrefixEmptyReferenceInput
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- Internal bridge for the miss already derived by query classification.
The real pointer resolver returns none and preserves the entire state. -/
theorem resolve_of_lookup {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (state : ValidityMachine.State K U) (address : UInt64)
    (miss : state.machine.user.addresses.allocIdFromAddr address 0
      (GlobalAddressLiveErrorExclusion.lookup state.machine.memory) = .ok none) :
    TypedValidityProviders.resolveAllocation pointers
      (Pointer.new (some .wildcard) (Size.ofBytes address)) state = .ok none state := by
  have resolution : state.machine.user.addresses.ptrGetAlloc
      (Pointer.new .wildcard (Size.ofBytes address)) 0
      (GlobalAddressLiveErrorExclusion.lookup state.machine.memory) pointers.arithmetic = .ok none := by
    simp only [GlobalAddressState.ptrGetAlloc,Pointer.new,Size.ofBytes,miss,
      bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
  simp only [Pointer.new,GlobalAddressLiveErrorExclusion.lookup] at resolution
  simp [TypedValidityProviders.resolveAllocation,PointerMachine.resolvePointer,Pointer.new,
    resolution,
    get,getThe,MonadStateOf.get,EStateM.get,set,EStateM.set,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,Id.run]

/-- Actual canonical zero-byte retag execution or the existing selected-hit
frontend data, derived internally from query-local raw representation. -/
theorem reborrow_or_hit {K U C F A : Type} [DecidableEq K]
    (context : ImageContext)
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared) (options : CompilerRetagOptions.Options)
    (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (budget : Nat) (place : MPlaceTy Provenance) (tag : BorTag)
    (state : ValidityMachine.State K U) (address : UInt64)
    (pointer : place.mplace.ptr = Pointer.new (some .wildcard) (Size.ofBytes address))
    (input : CurrentCallEmptySelectedHit.Query context state.machine.memory state.machine.user.addresses address) :
    TypedRetag.reborrow (EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler options) access projection vtable pointers choice)
      budget place Size.ZERO ChildBorrow.fnEntryPolicy tag state = .ok (some .wildcard) state ∨
    Nonempty (S03WildcardEmptyClassification.Hit context state.machine.memory state.machine.user.addresses address) := by
  rcases CurrentCallEmptySelectedHit.classify context state.machine.memory state.machine.user.addresses address input with miss | hit
  · apply Or.inl
    have check := RetagPointerChecks.check_pointer_zero access place.mplace.ptr state
    have resolve : TypedValidityProviders.resolveAllocation pointers place.mplace.ptr state = .ok none state := by
      rw [pointer]
      exact resolve_of_lookup pointers state address miss
    unfold TypedRetag.reborrow
    simp only [EvalRetagMachine.hooks,CompilerRetagOptions.make,check,resolve,
      bind,EStateM.bind,pure]
    simp [Size.ZERO,pointer,Pointer.new,EStateM.bind,EStateM.pure]
  · exact Or.inr hit

end DuplicatePrefix.CurrentCallEmptyMissOperation

open Lean Elab Command in
run_cmd do
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.contains "CurrentCallEmptyMissOperation" then
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved empty miss operation dependency {dependency}"
