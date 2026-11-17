import duplicate_prefix.RetagPointerChecks
import duplicate_prefix.RetagReferencePlace

/-! Actual pointer validity leaves used by shallow reference validation. -/
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace DuplicatePrefix.ReferenceChecks
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter

private theorem result_of_unit {K U : Type}
    (access : ValidityMachine.Access K U) (pointer : Pointer (Option Provenance)) (size : Size)
    (state : ValidityMachine.State K U)
    (unit : ValidityMachine.checkPointerAccess access pointer size state = .ok () state) :
    ValidityMachine.checkPointerAccessResult access pointer size state = .ok (.ok ()) state := by
  unfold ValidityMachine.checkPointerAccess at unit
  simp only [bind, EStateM.bind] at unit
  cases result : ValidityMachine.checkPointerAccessResult access pointer size state with
  | ok outcome after =>
    rw [result] at unit
    cases outcome with
    | ok value =>
      cases value
      change EStateM.Result.ok () after = .ok () state at unit
      cases unit
      rfl
    | error error =>
      change EStateM.Result.error _ after = .ok () state at unit
      cases unit
  | error error after =>
    rw [result] at unit
    cases unit

theorem check_result_cached {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (access : ValidityMachine.Access K U) (state : ValidityMachine.State K U)
    (id : AllocId) (tag : BorTag) (base offset len : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    ValidityMachine.checkPointerAccessResult access
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Size.ofBytes len) state =
      .ok (.ok ()) state :=
  result_of_unit access _ _ state (RetagPointerChecks.check_pointer_access_cached pointers access state
    id tag base offset len entry wiring width cached present positive signedFits bounds)

theorem check_result_zero {K U : Type} (access : ValidityMachine.Access K U)
    (pointer : Pointer (Option Provenance)) (state : ValidityMachine.State K U) :
    ValidityMachine.checkPointerAccessResult access pointer Size.ZERO state = .ok (.ok ()) state :=
  result_of_unit access pointer Size.ZERO state (RetagPointerChecks.check_pointer_zero access pointer state)

theorem alignment_one {K U : Type} (access : ValidityMachine.Access K U)
    (pointer : Pointer (Option Provenance)) (state : ValidityMachine.State K U) :
    ValidityMachine.checkPointerAlignResult access pointer Align.ONE state = .ok (.ok ()) state := by
  unfold ValidityMachine.checkPointerAlignResult
  simp [Align.ONE, Align.MAX, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, pure, EStateM.pure]

theorem pointer_integer (target : TargetDataLayout) (pointer : Pointer Provenance)
    (width : target.pointerWidth = .w64) :
    (Scalar.fromPointer target pointer).tryToScalarInt =
      .ok (.integer (ScalarInt.ofUInt64 pointer.offset.bytes)) := by
  have truncated := ScalarArithmetic.truncate_word pointer.offset.bytes
  unfold ScalarInt.truncateFromUInt at truncated
  unfold Scalar.tryToScalarInt Scalar.fromPointer ScalarInt.tryFromUInt
  unfold_internal ".Scalar.targetPointerSize"
  simp only [width, PointerWidth.bits, Size.fromBits]
  erw [truncated]
  rfl

private theorem nonzero_is_not_null (address : UInt64) (nonzero : address ≠ 0) :
    (ScalarInt.ofUInt64 address).isNull = false := by
  have wide : address.toNat < 2 ^ 128 := by
    have limit : address.toNat < 18446744073709551616 := address.toNat_lt_size
    omega
  unfold ScalarInt.isNull ScalarInt.ofUInt64
  apply Bool.eq_false_iff.mpr
  intro equal
  have value := congrArg BitVec.toNat ((beq_iff_eq).mp equal)
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt wide] at value
  apply nonzero
  apply UInt64.toNat_inj.mp
  simpa using value

theorem pointer_not_null {K U : Type} (target : TargetDataLayout) (pointer : Pointer Provenance)
    (width : target.pointerWidth = .w64) (nonzero : pointer.offset.bytes ≠ 0) :
    (ValidityMachine.scalarMayBeNull (K := K) (User := U) (Scalar.fromPointer target pointer)) =
      pure false := by
  unfold ValidityMachine.scalarMayBeNull
  rw [pointer_integer target pointer width]
  change pure ((ScalarInt.ofUInt64 pointer.offset.bytes).isNull) = pure false
  rw [nonzero_is_not_null pointer.offset.bytes nonzero]

theorem integer_not_null {K U : Type} (address : UInt64) (nonzero : address ≠ 0) :
    (ValidityMachine.scalarMayBeNull (K := K) (User := U)
      (Scalar.fromScalarInt (ScalarInt.ofUInt64 address))) = pure false := by
  unfold ValidityMachine.scalarMayBeNull
  change pure ((ScalarInt.ofUInt64 address).isNull) = pure false
  rw [nonzero_is_not_null address nonzero]

#print axioms check_result_cached
#print axioms alignment_one
#print axioms pointer_not_null
end DuplicatePrefix.ReferenceChecks
