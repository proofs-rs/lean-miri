import duplicate_prefix.CurrentCallFamilySatisfaction
import duplicate_prefix.RetagReferencePlace
import duplicate_prefix.RetagPointerChecks

/-! Actual optional-provenance decoding and physical positive ABI encoding.
An integer scalar is NOT an implicit wildcard cast. Logical Represents remains
a resource representation candidate; the positive reference ABI requires Some
provenance. Empty integer references keep their separate metadata interface. -/
namespace DuplicatePrefix.CurrentCallActualReferenceEncoding
open Miri Miri.ABI Miri.Memory Miri.DataStructures Miri.Interpreter Miri.Input
open Miri.TreeBorrows Miri.TreeBorrows.Tree
open CandidateStableCallOwnership CandidateCurrentJointCall CurrentCallSpatialCover CurrentCallFamilySatisfaction
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
noncomputable section

/-- The real scalar decoder preserves integer absence of provenance. -/
theorem integer_scalar (target : TargetDataLayout) (address : UInt64)
    (width : target.pointerWidth=.w64) :
    (Scalar.fromScalarInt (ScalarInt.ofUInt64 address) : Scalar Provenance).toPointer target=
      .ok (Pointer.withoutProvenance address) := RetagReferencePlace.integer_to_pointer target address width

/-- A None provenance pointer returns the REAL unresolved-address result
before any inverse-address/exposure lookup can run. -/
theorem resolve_none {K U : Type} (hooks : PointerMachine.Hooks K U)
    (memory : MemoryState Provenance BorrowTree K) (state : PointerMachine.State K U)
    (pointer : Pointer (Option Provenance)) (noProvenance : pointer.provenance=none) :
    PointerMachine.resolvePointer hooks memory state pointer 0=⟨state,.ok (.error pointer.offset.bytes)⟩ := by
  unfold PointerMachine.resolvePointer
  simp [noProvenance]

theorem allocation_none {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (pointer : Pointer (Option Provenance)) (state : ValidityMachine.State K U)
    (noProvenance : pointer.provenance=none) :
    TypedValidityProviders.resolveAllocation pointers pointer state=.ok none state :=
  RetagPointerChecks.resolve_allocation_none pointers pointer state noProvenance

/-- Run the actual pointer check, preserving any earlier error. If it returns,
the canonical resolver yields no allocation and nonzero reborrow rejects with
the interpreter's actual invalidProgram result. This is not a claim that every
earlier error is UB, or that representation alone admits a reference. -/
theorem reborrow_none {K U : Type} [DecidableEq K]
    (hooks : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (resolve : hooks.resolveAllocation=TypedValidityProviders.resolveAllocation pointers)
    (budget : Nat) (place : MPlaceTy Provenance) (size : Size)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) (state : ValidityMachine.State K U)
    (noProvenance : place.mplace.ptr.provenance=none) (nonzero : size.bytes≠0) :
    TypedRetag.reborrow hooks budget place size policy tag state=
      match hooks.checkPtrAccess place.mplace.ptr size state with
      | .error error after=>.error error after
      | .ok () after=>.error (.invalidProgram "nonzero reborrow without allocation") after := by
  unfold TypedRetag.reborrow
  cases check : hooks.checkPtrAccess place.mplace.ptr size state with
  | error error after => simp only [check,bind,EStateM.bind]
  | ok value after =>
    cases value
    have location:=allocation_none pointers place.mplace.ptr after noProvenance
    simp only [check,bind,EStateM.bind,resolve,location]
    simp [nonzero]
    rfl

theorem reborrow_none_rejects {K U : Type} [DecidableEq K]
    (hooks : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (resolve : hooks.resolveAllocation=TypedValidityProviders.resolveAllocation pointers)
    (budget : Nat) (place : MPlaceTy Provenance) (size : Size)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) (state : ValidityMachine.State K U)
    (noProvenance : place.mplace.ptr.provenance=none) (nonzero : size.bytes≠0) :
    ∀ value after,TypedRetag.reborrow hooks budget place size policy tag state≠.ok value after := by
  rw [reborrow_none hooks pointers resolve budget place size policy tag state noProvenance nonzero]
  cases hooks.checkPtrAccess place.mplace.ptr size state <;> simp

/-- Positive physical reference encoding, separate from current ownership,
initialization, mutability, layout and numeric execution readiness. -/
structure PositiveEncoding (argument : DuplicatePrefixSliceArgument.Argument) (place : MPlaceTy Provenance)
    (source ret : Family) : Prop where
  source : argument=.pointer source.value
  destination : place.mplace.ptr=ret.value.withOptionalProvenance

private theorem optional_injective {first second : Pointer Provenance}
    (same : first.withOptionalProvenance=second.withOptionalProvenance) : first=second := by
  cases first
  cases second
  cases same
  rfl

/-- Some decoded provenance implies the actual argument constructor is a
pointer, rather than conflating an integer with an exposed-address cast. -/
theorem source_of_decoded {argument : DuplicatePrefixSliceArgument.Argument} {value : Pointer Provenance}
    (decoded : DuplicatePrefixSliceArgument.placePointer argument=value.withOptionalProvenance) : argument=.pointer value := by
  cases argument with
  | pointer pointer => exact congrArg DuplicatePrefixSliceArgument.Argument.pointer (optional_injective decoded)
  | integer address =>
    have provenance:=congrArg Pointer.provenance decoded
    cases provenance

theorem of_decoded {argument place source ret}
    (sourceBits : DuplicatePrefixSliceArgument.placePointer argument=source.value.withOptionalProvenance)
    (returnBits : place.mplace.ptr=ret.value.withOptionalProvenance) : PositiveEncoding argument place source ret :=
  ⟨source_of_decoded sourceBits,returnBits⟩

theorem integer_not_positive (address : UInt64) (place : MPlaceTy Provenance) (source ret : Family) :
    ¬PositiveEncoding (.integer address) place source ret := by
  intro encoded
  cases encoded.source

theorem bool_some {argument place source ret} (encoded : PositiveEncoding argument place source ret) :
    place.mplace.ptr.provenance=some ret.value.provenance := by rw [encoded.destination];rfl

/-- The actual ABI scalar-pair is EXACTLY the pointer-encoded input consumed
by SpatialJointInstall.typed; no integer-to-wildcard operation is inserted. -/
theorem raw_value {argument place source ret} (encoded : PositiveEncoding argument place source ret)
    (target : TargetDataLayout) (len : UInt64) (layout : LocalLayout) :
    DuplicatePrefixSliceArgument.rawValue target argument len layout=
      RetagReferencePlace.sliceValue target source.value len layout := by rw [encoded.source];rfl

theorem first_value {argument place source ret} (encoded : PositiveEncoding argument place source ret)
    (target : TargetDataLayout) (len : UInt64) :
    DuplicatePrefixSliceArgument.first target argument len=
      ⟨.immediate (RetagReferencePlace.sliceValue target source.value len ActualReferenceMetadata.reference).imm,ActualReferenceMetadata.reference⟩ := by
  rw [encoded.source]
  rfl

/-- This necessity theorem consumes an actual returned result; it is not an
operation-success field in the physical ABI or ownership specification. -/
theorem some_of_reborrow {K U : Type} [DecidableEq K]
    (hooks : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (resolve : hooks.resolveAllocation=TypedValidityProviders.resolveAllocation pointers)
    (budget : Nat) (place : MPlaceTy Provenance) (size : Size)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) (state : ValidityMachine.State K U)
    (nonzero : size.bytes≠0) (value : Option Provenance) (after : ValidityMachine.State K U)
    (returned : TypedRetag.reborrow hooks budget place size policy tag state=.ok value after) :
    ∃ provenance,place.mplace.ptr.provenance=some provenance := by
  cases provenance : place.mplace.ptr.provenance with
  | some value => exact ⟨value,rfl⟩
  | none => exact False.elim ((reborrow_none_rejects hooks pointers resolve budget place size policy tag state provenance nonzero value after) returned)

theorem source_optional {argument place source ret} (encoded : PositiveEncoding argument place source ret) :
    DuplicatePrefixSliceArgument.placePointer argument=source.value.withOptionalProvenance := by rw [encoded.source];rfl

/-- Form EXACTLY the two current ABI occurrence annotations, retaining the
already assigned family payloads and IDs. This is a projection of actual ABI
values, not a copy/retag execution theorem or identity inferred from equal bits. -/
def abi {actual : Array (Pointer (Option Provenance))} (a : Assignment actual)
    {argument place source ret} (encoded : PositiveEncoding argument place source ret)
    (sourceAt : a.families[source.slot]?=some ⟨source.allocation,source.value⟩)
    (returnAt : a.families[ret.slot]?=some ⟨ret.allocation,ret.value⟩) :
    Assignment #[DuplicatePrefixSliceArgument.placePointer argument,place.mplace.ptr] where
  families:=a.families
  references:=#[some source.slot,some ret.slot]
  size:=rfl
  coherent:=by
    intro occurrence identity found
    have bound : occurrence<2 := (Array.getElem?_eq_some_iff.mp found).1
    have alternatives : occurrence=0 ∨ occurrence=1 := by omega
    rcases alternatives with zero | one
    · subst occurrence
      have same : identity=source.slot := by simpa using found.symm
      subst identity
      refine ⟨⟨source.allocation,source.value⟩,sourceAt,DuplicatePrefixSliceArgument.placePointer argument,rfl,?_⟩
      rw [source_optional encoded]
      exact ⟨rfl,rfl⟩
    · subst occurrence
      have same : identity=ret.slot := by simpa using found.symm
      subst identity
      refine ⟨⟨ret.allocation,ret.value⟩,returnAt,place.mplace.ptr,rfl,?_⟩
      rw [encoded.destination]
      exact ⟨rfl,rfl⟩

theorem abi_source {actual : Array (Pointer (Option Provenance))} (a : Assignment actual)
    {argument place source ret} (encoded : PositiveEncoding argument place source ret)
    (sourceAt : a.families[source.slot]?=some ⟨source.allocation,source.value⟩)
    (returnAt : a.families[ret.slot]?=some ⟨ret.allocation,ret.value⟩) :
    (abi a encoded sourceAt returnAt).Binds 0 source := ⟨sourceAt,rfl⟩

theorem abi_return {actual : Array (Pointer (Option Provenance))} (a : Assignment actual)
    {argument place source ret} (encoded : PositiveEncoding argument place source ret)
    (sourceAt : a.families[source.slot]?=some ⟨source.allocation,source.value⟩)
    (returnAt : a.families[ret.slot]?=some ⟨ret.allocation,ret.value⟩) :
    (abi a encoded sourceAt returnAt).Binds 1 ret := ⟨returnAt,rfl⟩

theorem abi_preserves_families {actual : Array (Pointer (Option Provenance))} (a : Assignment actual)
    {argument place source ret} (encoded : PositiveEncoding argument place source ret)
    (sourceAt : a.families[source.slot]?=some ⟨source.allocation,source.value⟩)
    (returnAt : a.families[ret.slot]?=some ⟨ret.allocation,ret.value⟩) :
    (abi a encoded sourceAt returnAt).families=a.families := rfl


/-- The actual integer scalar-pair constructor yields this None-provenance
place. For u8 metadata, the actual dynamic byte size is len; the existing layout
lemmas provide that tie when this specialization is used by the typed driver. -/
theorem integer_slice_rejects {K U : Type} [DecidableEq K]
    (hooks : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (resolve : hooks.resolveAllocation=TypedValidityProviders.resolveAllocation pointers)
    (budget : Nat) (address len : UInt64) (pointee : LocalLayout)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) (state : ValidityMachine.State K U)
    (positive : 0<len.toNat) :
    ∀ value after,TypedRetag.reborrow hooks budget (RetagReferencePlace.integerSlicePlace address len pointee)
      (Size.ofBytes len) policy tag state≠.ok value after := by
  apply reborrow_none_rejects hooks pointers resolve budget _ _ policy tag state
  · rfl
  · intro zero
    change len=0 at zero
    rw [zero] at positive
    cases positive

/-- The destination condition is independently usable for the empty-source
branch; it requires no source family or source pointer encoding. -/
theorem destination_some (place : MPlaceTy Provenance) (ret : Family)
    (decoded : place.mplace.ptr=ret.value.withOptionalProvenance) :
    place.mplace.ptr.provenance=some ret.value.provenance := by rw [decoded];rfl


end
end DuplicatePrefix.CurrentCallActualReferenceEncoding
