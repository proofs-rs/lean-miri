import empty_function.IndirectWildcardFootprint
import empty_function.ConcreteProtection
namespace EmptyFunction.IndirectProjection
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input
open EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.InputDraft
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem checked_bounds (target : PointerArithmetic) (id : AllocId) (capacity offset : Size)
    (count : Nat) (signedFits : count < 2^63) (inBounds : offset.bytes.toNat+count ≤ capacity.bytes.toNat) :
    checkedBounds target id capacity offset (count : Int) .inboundsPointerArithmetic = .ok () := by
  simp [checkedBounds]
  split
  · rename_i bad
    change (decide (-(2^63 : Int) ≤ (count : Int)) && decide ((count : Int) < (2^63 : Int))) = false at bad
    simp at bad
    omega
  · simp [Nat.not_lt.mpr inBounds]
    rfl

private theorem checked_access (target : PointerArithmetic) (pointer : Pointer (Option Provenance))
    (count : Nat) (id : AllocId) (relative : Size) (info : AllocationInfo) (provenance : Provenance)
    (resolve : PointerResolver Provenance Provenance) (lookup : LiveAllocationLookup)
    (positive : 0 < count) (signedFits : count < 2^63)
    (resolved : resolve pointer (count : Int) = .ok ⟨id,relative,provenance⟩)
    (known : lookup id = .ok info) (live : info.kind ≠ .dead)
    (bounds : relative.bytes.toNat+count ≤ info.size.bytes.toNat) :
    checkAndDerefPtr target pointer (count : Int) .inboundsPointerArithmetic resolve lookup =
      .ok (some ⟨⟨id,relative,provenance⟩,info⟩) := by
  have interval := checked_bounds target id info.size relative count signedFits bounds
  simp [checkAndDerefPtr,Nat.ne_of_gt positive]
  split
  · rename_i bad
    change (decide (-(2^63 : Int) ≤ (count : Int)) && decide ((count : Int) < (2^63 : Int))) = false at bad
    simp at bad
    omega
  · rw [resolved]
    simp [known,live]
    rw [interval]
    rfl

theorem positive (s : Static) (metadata : Metadata s) (before : State)
    (place : MemPlace Provenance) (length amount : Size)
    (foot : IndirectFootprint before place.ptr length) (tables : place.ptr.provenance = some .wildcard → AddressTables before)
    (positive : amount.bytes ≠ 0) (within : amount.bytes.toNat ≤ length.bytes.toNat)
    (signedLength : length.bytes.toNat < 2^63) :
    EvalProjectionMachine.memoryOffset (ConcreteProtection.source s).pointers before place amount .inbounds .none =
      .ok {place with ptr := {place.ptr with offset := Size.ofBytes (place.ptr.offset.bytes+amount.bytes)},metadata := .none} := by
  have positiveNat : 0 < amount.bytes.toNat := by
    have ne : amount.bytes.toNat ≠ 0 := by intro zero;apply positive;exact UInt64.toNat_inj.mp zero
    omega
  have parentPositive : length.bytes ≠ 0 := by
    intro zero
    have bound := within
    rw [zero] at bound
    simp only [UInt64.toNat_zero] at bound
    omega
  have fits : amount.bytes.toNat < 2^63 := by omega
  have signed : (Int64.ofInt (amount.bytes.toNat : Int)).toInt = (amount.bytes.toNat : Int) :=
    Int64.toInt_ofInt_of_le (by omega) (Int.ofNat_lt.mpr fits)
  have signedWord : (Int64.ofInt (amount.bytes.toNat : Int)).toUInt64 = amount.bytes := by
    rw [Int64.ofInt_eq_ofNat]
    exact UInt64.ofNat_toNat
  have encoding : ∃ provenance, place.ptr.provenance = some provenance := by
    cases enc : place.ptr.provenance with
    | none => have impossible := foot.attribution;simpa only [enc] using impossible
    | some provenance => exact ⟨provenance,rfl⟩
  obtain ⟨provenance,encoding⟩ := encoding
  let arithmetic := (ConcreteProtection.source s).pointers.arithmetic
  have truncate : ∀ value, arithmetic.truncateToTargetUsize value = .ok value :=
    ConcreteProtection.source_truncate s metadata.pointerSize
  have pointerGet := IndirectWildcardFootprint.pointer before place.ptr length foot parentPositive provenance encoding tables
    arithmetic truncate (Int64.ofInt (amount.bytes.toNat : Int)) (by rw [signed];omega)
  have info : before.machine.memory.getAllocInfo foot.id =
      .ok ⟨foot.entry.allocation.byteSize,foot.entry.allocation.align,.liveData,foot.entry.allocation.mutability⟩ := by
    simp [MemoryState.getAllocInfo,foot.live,Except.pure]
    rfl
  let resolve : PointerResolver Provenance Provenance := fun _ _ =>
    .ok ⟨foot.id,Size.ofBytes foot.relative,provenance⟩
  have bounds : foot.relative.toNat+amount.bytes.toNat ≤ foot.entry.allocation.byteSize.bytes.toNat := by
    have bound := foot.extent
    omega
  have accessed := checked_access arithmetic place.ptr amount.bytes.toNat foot.id (Size.ofBytes foot.relative)
    ⟨foot.entry.allocation.byteSize,foot.entry.allocation.align,.liveData,foot.entry.allocation.mutability⟩ provenance
    resolve before.machine.memory.getAllocInfo positiveNat fits rfl info (by change AllocationKind.liveData ≠ .dead;decide) bounds
  have offsetChecked : ptrOffsetInbounds arithmetic place.ptr (Int64.ofInt (amount.bytes.toNat : Int)) resolve
      before.machine.memory.getAllocInfo =
      .ok {place.ptr with offset := Size.ofBytes (place.ptr.offset.bytes+amount.bytes)} := by
    unfold ptrOffsetInbounds checkPtrAccessSigned
    rw [signed,accessed]
    simp only [Except.mapError,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
    unfold Pointer.wrappingSignedOffset Pointer.wrappingOffset
    rw [signedWord,truncate]
    rfl
  have nonzero : amount ≠ Size.ZERO := by intro same;apply positive;rw [same];rfl
  simp only [WildcardResolution.lookup] at pointerGet
  simp [EvalProjectionMachine.memoryOffset,MemPlaceMeta.hasMeta,fits,Nat.not_le.mpr fits,
    nonzero,encoding,pointerGet,Except.mapError,projectionMemoryOffset,MemPlace.offsetWithMeta,
    offsetChecked,resolve,arithmetic,bind,Bind.bind,Except.bind,pure,Pure.pure,Except.pure]
end EmptyFunction.IndirectProjection
