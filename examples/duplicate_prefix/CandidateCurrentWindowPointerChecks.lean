import duplicate_prefix.ActualReferenceContext
import duplicate_prefix.ActualRetagContext
import duplicate_prefix.CandidateCallBindings
import duplicate_prefix.GeneralBorrowPositiveWildcardWindowPointerChecks

/-! Actual pointer checks for normalized interior current-call windows. Both
concrete and wildcard provenance retain their exact allocation-relative offset.
No access-success or metadata-cache premise is supplied. -/
namespace DuplicatePrefix.CandidateCurrentWindowPointerChecks
open Miri Miri.ABI Miri.Memory Miri.Input Miri.Interpreter
open Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

def extraOf (provenance : Provenance) : ProvenanceExtra :=
  match provenance with | .concrete _ tag => .concrete tag | .wildcard => .wildcard

theorem with_pointers
    (access : ValidityMachine.Access MiriMemoryKind CanonicalConfigFacts.RootStored)
    (pointers : CanonicalConfigFacts.RootPointers)
    (resolve : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (arithmetic : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (state : ValidityMachine.State MiriMemoryKind CanonicalConfigFacts.RootStored)
    (pointer : Pointer Provenance) (id : AllocId) (offset : Nat) (len : UInt64)
    (binding : CandidateCallBindings.WindowBinding state.machine pointer id offset len.toNat)
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808) :
    ValidityMachine.checkPointerAccess access
      pointer.withOptionalProvenance (Size.ofBytes len) state = .ok () state ∧
    TypedValidityProviders.resolveAllocation pointers pointer.withOptionalProvenance state =
      .ok (some ⟨id,Size.ofBytes (UInt64.ofNat offset),extraOf pointer.provenance⟩) state := by
  obtain ⟨entry,base,present,cached,byteLength,room,bounds,addressEq,_,provenance⟩ := binding
  have offsetBound : offset < 2^64 := by omega
  have offsetEq : (UInt64.ofNat offset).toNat = offset := by
    simp only [UInt64.toNat_ofNat',Nat.mod_eq_of_lt offsetBound]
  have sumEq : (base+UInt64.ofNat offset).toNat = base.toNat+offset := by
    simp only [UInt64.toNat_add,offsetEq,Nat.mod_eq_of_lt (by omega : base.toNat+offset<2^64)]
  have bits : pointer.offset.bytes = base+UInt64.ofNat offset := UInt64.toNat_inj.mp (addressEq.trans sumEq.symm)
  have physical : (UInt64.ofNat offset).toNat+len.toNat ≤ entry.allocation.byteSize.bytes.toNat := by
    rw [offsetEq];omega
  have positiveUInt : (0 : UInt64) < len := by simpa only [UInt64.lt_iff_toNat_lt,UInt64.toNat_zero] using positive
  cases prov : pointer.provenance with
  | concrete supplied tag =>
    have same : supplied = id := by simpa [prov] using provenance
    subst supplied
    have pointerEq : pointer.withOptionalProvenance =
        Pointer.new (some (.concrete id tag)) (Size.ofBytes (base+UInt64.ofNat offset)) := by
      cases pointer with | mk pointerOffset pointerProvenance =>
        cases pointerOffset
        simp_all [Pointer.withOptionalProvenance,Pointer.new,Size.ofBytes]
    rw [pointerEq]
    exact ⟨RetagPointerChecks.check_pointer_access_cached pointers _ state id tag base _ len entry
      resolve arithmetic cached present positiveUInt signedFits physical,
      by simpa [extraOf,prov] using (RetagPointerChecks.resolve_allocation_cached pointers state id tag base
        (UInt64.ofNat offset) arithmetic cached)⟩
  | wildcard =>
    have wild : state.machine.user.addresses.provenanceMode ≠ .strict ∧
        state.machine.user.addresses.exposed.contains id = true ∧
        WildcardGeneralHitReborrow.Geometry state.machine.user.addresses.intToPtrMap
          pointer.offset.bytes base id entry.allocation.byteSize := by
      simpa only [prov] using provenance
    obtain ⟨mode,exposed,geometry⟩ := wild
    have pointerEq : pointer.withOptionalProvenance =
        Pointer.new (some .wildcard) (Size.ofBytes (base+UInt64.ofNat offset)) := by
      cases pointer with | mk pointerOffset pointerProvenance =>
        cases pointerOffset
        simp_all [Pointer.withOptionalProvenance,Pointer.new,Size.ofBytes]
    have geometry' : WildcardGeneralHitReborrow.Geometry state.machine.user.addresses.intToPtrMap
        (base+UInt64.ofNat offset) base id entry.allocation.byteSize := by rw [←bits];exact geometry
    rw [pointerEq]
    refine ⟨GeneralBorrowPositiveWildcardWindowPointerChecks.check pointers _ state base _ len id entry
      geometry' resolve arithmetic mode exposed cached present positiveUInt signedFits physical,?_⟩
    have resolved := WildcardGeneralHitReborrow.resolve pointers state (base+UInt64.ofNat offset) base id
      entry geometry' arithmetic mode exposed cached present
    have relative : base+UInt64.ofNat offset-base = UInt64.ofNat offset := by
      rw [UInt64.add_comm base _,UInt64.add_sub_cancel]
    simpa only [relative,extraOf,prov] using resolved

theorem actual (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualReferenceContext.Context options remaining span)
    (state : ValidityMachine.State MiriMemoryKind CanonicalConfigFacts.RootStored)
    (pointer : Pointer Provenance) (id : AllocId) (offset : Nat) (len : UInt64)
    (binding : CandidateCallBindings.WindowBinding state.machine pointer id offset len.toNat)
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808) :
    ValidityMachine.checkPointerAccess (ActualReferenceContext.config options remaining span).access
      pointer.withOptionalProvenance (Size.ofBytes len) state = .ok () state ∧
    TypedValidityProviders.resolveAllocation ctx.pointers pointer.withOptionalProvenance state =
      .ok (some ⟨id,Size.ofBytes (UInt64.ofNat offset),extraOf pointer.provenance⟩) state :=
  with_pointers _ ctx.pointers ctx.resolve ctx.arithmetic state pointer id offset len binding positive signedFits

theorem actual_retag (options : EvalConfigurationCore.Options) (remaining : Nat)
    (span : PreparedContracts.FixedSpanQuery)
    (ctx : ActualRetagContext.Context options remaining span)
    (state : ValidityMachine.State MiriMemoryKind CanonicalConfigFacts.RootStored)
    (pointer : Pointer Provenance) (id : AllocId) (offset : Nat) (len : UInt64)
    (binding : CandidateCallBindings.WindowBinding state.machine pointer id offset len.toNat)
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808) :
    ValidityMachine.checkPointerAccess (ActualReferenceContext.config options remaining span).access
      pointer.withOptionalProvenance (Size.ofBytes len) state = .ok () state ∧
    TypedValidityProviders.resolveAllocation ctx.pointers pointer.withOptionalProvenance state =
      .ok (some ⟨id,Size.ofBytes (UInt64.ofNat offset),extraOf pointer.provenance⟩) state :=
  with_pointers _ ctx.pointers ctx.resolve ctx.arithmetic state pointer id offset len binding positive signedFits

end DuplicatePrefix.CandidateCurrentWindowPointerChecks

open Lean Elab Command in
run_cmd do
  for (name, _) in (← getEnv).constants.toList do
    if name.toString.startsWith "DuplicatePrefix.CandidateCurrentWindowPointerChecks." then
      for dependency in (← collectAxioms name) do
        unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
          throwError "unapproved current window pointer dependency {dependency}"
