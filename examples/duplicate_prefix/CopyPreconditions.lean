import duplicate_prefix.RootBody
import Lean.Elab.Deriving.ToExpr
import duplicate_prefix.ScalarArithmetic
import duplicate_prefix.ScalarOperations
import duplicate_prefix.PointerArithmetic
import Miri.Interpreter.PointerMachine
import Miri.Interpreter.IntrinsicAtomic
import Miri.Interpreter.IntegerCast
import Miri.Memory.AllocAddresses

/-! Scalar operations executed by the pinned standard-library copy checks.
The statements concern production integer/pointer evaluators, not a recoding
of the Rust predicates. -/
namespace DuplicatePrefix.CopyPreconditions
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
open DuplicatePrefix.ScalarArithmetic
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem usize_one_mul (value : UInt64) :
    IntegerOps.binary .MulWithOverflow (usizeValue 1) (usizeValue value) =
      .ok (.withOverflow (ScalarInt.ofUInt64 value) false) := by
  unfold IntegerOps.binary
  rw [decode_usize, decode_usize]
  simp only [bind, Except.bind]
  simp [usizeValue]
  simp_scalar_implementation
  have bound : value.toNat < 18446744073709551616 := value.toNat_lt_size
  have wide : value.toNat < 340282366920938463463374607431768211456 := by omega
  have bits : BitVec.setWidth 128 (BitVec.ofNat 64
      (value.toNat % 340282366920938463463374607431768211456)) =
      BitVec.ofNat 128 value.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt wide]
  simp [bits, ScalarInt.ofUInt64, Size.ofBytes]
  omega

def u64Value (value : UInt64) : IntegerValue :=
  ⟨ScalarInt.ofUInt64 value, ⟨Size.ofBytes 8,.u64⟩⟩

theorem scalar_word_bits (value : UInt64) :
    (ScalarInt.ofUInt64 value).toUInt (Size.ofBytes 8) = .ok (BitVec.ofNat 128 value.toNat) := by rfl

theorem decode_u64 (value : UInt64) :
    IntegerOps.decode (u64Value value) = .ok (Int.ofNat value.toNat) := by
  have bound : value.toNat < 2 ^ 128 := by
    have smaller : value.toNat < 18446744073709551616 := value.toNat_lt_size
    omega
  simp [IntegerOps.decode, u64Value, IntegerType.signed, IntegerKind.signed,
    scalar_word_bits, BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound,
    Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem u64_one_mul (value : UInt64) :
    IntegerOps.binary .MulWithOverflow (u64Value 1) (u64Value value) =
      .ok (.withOverflow (ScalarInt.ofUInt64 value) false) := by
  unfold IntegerOps.binary
  rw [decode_u64, decode_u64]
  simp only [bind, Except.bind]
  simp [u64Value]
  simp_scalar_implementation
  have bound : value.toNat < 18446744073709551616 := value.toNat_lt_size
  have wide : value.toNat < 340282366920938463463374607431768211456 := by omega
  have bits : BitVec.setWidth 128 (BitVec.ofNat 64
      (value.toNat % 340282366920938463463374607431768211456)) =
      BitVec.ofNat 128 value.toNat := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt wide]
  simp [bits, ScalarInt.ofUInt64, Size.ofBytes]
  omega
theorem usize_sub_bounded (left right : UInt64) (lower : right.toNat ≤ left.toNat) :
    IntegerOps.binary .SubWithOverflow (usizeValue left) (usizeValue right) =
      .ok (.withOverflow (ScalarInt.ofUInt64 (left - right)) false) := by
  unfold IntegerOps.binary
  rw [decode_usize, decode_usize]
  simp only [bind, Except.bind]
  simp [usizeValue]
  simp_scalar_implementation
  have difference : (left.toNat : Int) - right.toNat = Int.ofNat (left.toNat - right.toNat) := (Int.ofNat_sub lower).symm
  have resultFits : left.toNat - right.toNat < 18446744073709551616 := by
    have bound : left.toNat < 18446744073709551616 := left.toNat_lt_size
    omega
  have wide : left.toNat - right.toNat < 340282366920938463463374607431768211456 := by omega
  rw [difference]
  try simp only [BitVec.ofInt_natCast, BitVec.toNat_ofNat, Nat.mod_eq_of_lt wide]
  have subNat : (left - right).toNat = left.toNat - right.toNat :=
    UInt64.toNat_sub_of_le left right (UInt64.le_iff_toNat_le.mpr lower)
  have bits : BitVec.setWidth 128 (BitVec.ofNat 64 (left.toNat - right.toNat)) =
      BitVec.ofNat 128 (left.toNat - right.toNat) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt resultFits, Nat.mod_eq_of_lt wide]
  simp [bits, ScalarInt.ofUInt64, Size.ofBytes, subNat, resultFits, Nat.mod_eq_of_lt wide]
  omega

theorem usize_lt (left right : UInt64) :
    IntegerOps.binary .Lt (usizeValue left) (usizeValue right) = .ok (.boolean (left < right)) := by
  unfold IntegerOps.binary
  rw [decode_usize, decode_usize]
  simp [usizeValue, bind, Except.bind, pure, Except.pure, UInt64.lt_iff_toNat_lt]

theorem usize_ge (left right : UInt64) :
    IntegerOps.binary .Ge (usizeValue left) (usizeValue right) = .ok (.boolean (right ≤ left)) := by
  unfold IntegerOps.binary
  rw [decode_usize, decode_usize]
  simp [usizeValue, bind, Except.bind, pure, Except.pure, UInt64.le_iff_toNat_le]

theorem usize_bitand_zero (value : UInt64) :
    IntegerOps.binary .BitAnd (usizeValue value) (usizeValue 0) =
      .ok (.scalar (ScalarInt.ofUInt64 0)) := by
  unfold IntegerOps.binary
  rw [decode_usize, decode_usize]
  simp [usizeValue]
  have toUInt (n : UInt64) : (ScalarInt.ofUInt64 n).toUInt (Size.ofBytes 8) = .ok (BitVec.ofNat 128 n.toNat) := by
    have bound : n.toNat < 2 ^ 128 := by
      have smaller : n.toNat < 18446744073709551616 := n.toNat_lt_size
      omega
    simp [ScalarInt.toUInt, ScalarInt.toBits, ScalarInt.ofUInt64, Size.ofBytes,
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  rw [toUInt value, toUInt 0]
  simp [Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]
  decide +kernel


theorem count_ones_one : IntegerIntrinsic.run .ctpop (ScalarInt.ofUInt64 1)
    ⟨Size.ofBytes 8,.usize⟩ ⟨Size.ofBytes 4,.u32⟩ = .ok (ScalarInt.ofUInt32 1) := by decide +kernel


open Lean Elab Tactic in
elab "unfold_copy " suffix:str : tactic => do
  let found := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix.getString then some name else none
  let [name] := found | throwError "expected one source constant {suffix.getString}"
  evalTactic (← `(tactic| unfold $(mkIdent name)))

theorem integer_cast_word (sourceKind targetKind : IntegerKind) (value : UInt64)
    (unsigned : sourceKind.signed = false) :
    IntegerCast.cast (.integer ⟨Size.ofBytes 8,sourceKind⟩) (ScalarInt.ofUInt64 value)
      (.integer ⟨Size.ofBytes 8,targetKind⟩) = .ok (ScalarInt.ofUInt64 value) := by
  have bound : value.toNat < 2 ^ 128 := by
    have smaller : value.toNat < 18446744073709551616 := value.toNat_lt_size
    omega
  unfold IntegerCast.cast
  unfold_copy ".Miri.Interpreter.IntegerCast.sourceValue"
  simp only [IntegerType.signed, unsigned, Bool.false_eq_true, ↓reduceIte,
    scalar_word_bits, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]
  rw [truncate_word value]

theorem pointer_to_scalar_int (target : TargetDataLayout) (pointer : Pointer Provenance)
    (width : target.pointerWidth = .w64) :
    (Scalar.fromPointer target pointer).toScalarInt = .ok (ScalarInt.ofUInt64 pointer.offset.bytes) := by
  have truncated := truncate_word pointer.offset.bytes
  unfold ScalarInt.truncateFromUInt at truncated
  unfold Scalar.toScalarInt Scalar.tryToScalarInt Scalar.fromPointer
  unfold_copy ".Miri.Memory.Scalar.targetPointerSize"
  have addressProv : PointerProvenance.offsetIsAddr (Prov := Provenance) = true := rfl
  simp only [width, addressProv, Bool.true_eq, ↓reduceIte]
  simp only [show Size.fromBits PointerWidth.w64.bits = Size.ofBytes 8 from rfl]
  unfold ScalarInt.tryFromUInt
  rw [truncated]
  rfl

theorem pointer_to_bits (target : TargetDataLayout) (pointer : Pointer Provenance)
    (width : target.pointerWidth = .w64) :
    (Scalar.fromPointer target pointer).toBits (Size.ofBytes 8) = .ok (BitVec.ofNat 128 pointer.offset.bytes.toNat) := by
  unfold Scalar.toBits
  rw [pointer_to_scalar_int target pointer width]
  simp [ScalarInt.toBits, ScalarInt.ofUInt64, Size.ofBytes, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem adjacent_subtraction (source n : UInt64)
    (fits : source.toNat + n.toNat < 18446744073709551616) :
    IntegerOps.binary .SubWithOverflow (usizeValue (source + n)) (usizeValue source) =
      .ok (.withOverflow (ScalarInt.ofUInt64 n) false) := by
  have destNat : (source + n).toNat = source.toNat + n.toNat := by
    simp [UInt64.toNat_add, Nat.mod_eq_of_lt fits]
  have result := usize_sub_bounded (source + n) source (by omega)
  have sub : source + n - source = n := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by omega)), destNat]
    omega
  simpa only [sub] using result

theorem source_nonzero_destination_nonzero (source n : UInt64)
    (fits : source.toNat + n.toNat < 18446744073709551616)
    (nonzero : source ≠ 0) : source + n ≠ 0 := by
  intro zero
  have result : (source + n).toNat = 0 := congrArg UInt64.toNat zero
  simp only [UInt64.toNat_add, Nat.mod_eq_of_lt fits] at result
  have sourceZero : source.toNat = 0 := by omega
  exact nonzero (UInt64.toNat_inj.mp sourceZero)

theorem scalar_usize_one_mul [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov State Choice) (choice : Choice)
    (layout overflowLayout : LocalLayout) (value : UInt64)
    (classification : hooks.classify choice layout.ty = pure (.integer .usize))
    (resultLayout : hooks.overflowLayout choice layout = pure overflowLayout)
    (width : layout.layout.size = Size.ofBytes 8) :
    ScalarOps.binary hooks choice .MulWithOverflow (ScalarOperations.usizeImmediate 1 layout) (ScalarOperations.usizeImmediate value layout) =
      pure (⟨.scalarPair (.fromScalarInt (.ofUInt64 value)) (.fromBool false), overflowLayout⟩ : RvalueImmTy Prov) := by
  have operation := usize_one_mul value
  simp only [usizeValue, ScalarInt.ofUInt64] at operation
  funext state
  simp_scalar_dispatch

theorem scalar_u64_one_mul [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov State Choice) (choice : Choice)
    (layout overflowLayout : LocalLayout) (value : UInt64)
    (classification : hooks.classify choice layout.ty = pure (.integer .u64))
    (resultLayout : hooks.overflowLayout choice layout = pure overflowLayout)
    (width : layout.layout.size = Size.ofBytes 8) :
    ScalarOps.binary hooks choice .MulWithOverflow (ScalarOperations.usizeImmediate 1 layout) (ScalarOperations.usizeImmediate value layout) =
      pure (⟨.scalarPair (.fromScalarInt (.ofUInt64 value)) (.fromBool false), overflowLayout⟩ : RvalueImmTy Prov) := by
  have operation := u64_one_mul value
  simp only [u64Value, ScalarInt.ofUInt64] at operation
  funext state
  simp_scalar_dispatch

theorem scalar_usize_sub_bounded [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov State Choice) (choice : Choice)
    (layout overflowLayout : LocalLayout) (left right : UInt64)
    (classification : hooks.classify choice layout.ty = pure (.integer .usize))
    (resultLayout : hooks.overflowLayout choice layout = pure overflowLayout)
    (width : layout.layout.size = Size.ofBytes 8)
    (lower : right.toNat ≤ left.toNat) :
    ScalarOps.binary hooks choice .SubWithOverflow (ScalarOperations.usizeImmediate left layout) (ScalarOperations.usizeImmediate right layout) =
      pure (⟨.scalarPair (.fromScalarInt (.ofUInt64 (left - right))) (.fromBool false), overflowLayout⟩ : RvalueImmTy Prov) := by
  have operation := usize_sub_bounded left right lower
  simp only [usizeValue, ScalarInt.ofUInt64] at operation
  funext state
  simp_scalar_dispatch

theorem scalar_usize_bitand_zero [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov State Choice) (choice : Choice)
    (layout : LocalLayout) (value : UInt64)
    (classification : hooks.classify choice layout.ty = pure (.integer .usize))
    (width : layout.layout.size = Size.ofBytes 8) :
    ScalarOps.binary hooks choice .BitAnd (ScalarOperations.usizeImmediate value layout) (ScalarOperations.usizeImmediate 0 layout) =
      pure (ScalarOperations.usizeImmediate 0 layout : RvalueImmTy Prov) := by
  have operation := usize_bitand_zero value
  simp only [usizeValue, ScalarInt.ofUInt64] at operation
  funext state
  simp_scalar_dispatch

theorem scalar_usize_ge [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov State Choice) (choice : Choice)
    (layout boolLayout : LocalLayout) (left right : UInt64)
    (classification : hooks.classify choice layout.ty = pure (.integer .usize))
    (resultLayout : hooks.boolLayout choice = pure boolLayout)
    (width : layout.layout.size = Size.ofBytes 8) :
    ScalarOps.binary hooks choice .Ge (ScalarOperations.usizeImmediate left layout) (ScalarOperations.usizeImmediate right layout) =
      pure (⟨.scalar (.fromBool (right ≤ left)), boolLayout⟩ : RvalueImmTy Prov) := by
  have operation := usize_ge left right
  simp only [usizeValue, ScalarInt.ofUInt64] at operation
  funext state
  simp_scalar_dispatch


theorem cached_base_address (hooks : PointerMachine.Hooks K U) (state : PointerMachine.State K U)
    (id : AllocId) (base : UInt64) (kind : Option AllocAddresses.AddressMemoryKind)
    (choices : AllocAddresses.AddressRandomChoices)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩) :
    PointerMachine.addrFromAllocId hooks id kind choices state = .ok base state := by
  unfold PointerMachine.addrFromAllocId
  unfold_copy ".Miri.Interpreter.PointerMachine.addresses"
  simp [cached, get, getThe, MonadStateOf.get, EStateM.get, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

theorem cached_root_pointer (hooks : PointerMachine.Hooks K U) (state : PointerMachine.State K U)
    (id : AllocId) (tag : BorTag) (base : UInt64) (offset : Size)
    (kind : AllocAddresses.AddressMemoryKind) (choices : AllocAddresses.AddressRandomChoices)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩) :
    PointerMachine.adjustAllocRootPointer hooks id tag offset kind choices state =
      .ok (Pointer.new (.concrete id tag) (Size.ofBytes (base + offset.bytes))) state := by
  have assigned := cached_base_address hooks state id base (some kind) choices cached
  have wrapped := PointerArithmetic.wrapping_offset_u64
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes base)) offset
  change (Pointer.new (Provenance.concrete id tag) (Size.ofBytes base)).wrappingOffset offset ⟨Size.ofBytes 8⟩ = _ at wrapped
  unfold PointerMachine.adjustAllocRootPointer
  simp only [Bind.bind, EStateM.bind, assigned]
  rw [width]
  rw [wrapped]
  rfl

theorem cached_byte_slice_checks (base offset n capacity : UInt64)
    (basePositive : 0 < base.toNat)
    (allocationFits : base.toNat + capacity.toNat < 18446744073709551616)
    (copyFits : offset.toNat + n.toNat + n.toNat ≤ capacity.toNat)
    (nonzero : n ≠ 0) :
    let source := base + offset
    let destination := source + n
    source ≠ 0 ∧ destination ≠ 0 ∧
      IntegerOps.binary .MulWithOverflow (usizeValue 1) (usizeValue n) = .ok (.withOverflow (ScalarInt.ofUInt64 n) false) ∧
      IntegerOps.binary .SubWithOverflow (usizeValue destination) (usizeValue source) = .ok (.withOverflow (ScalarInt.ofUInt64 n) false) ∧
      IntegerOps.binary .Lt (usizeValue source) (usizeValue destination) = .ok (.boolean true) ∧
      IntegerOps.binary .Ge (usizeValue n) (usizeValue n) = .ok (.boolean true) ∧
      IntegerOps.binary .Eq (usizeValue source) (usizeValue 0) = .ok (.boolean false) ∧
      IntegerOps.binary .Eq (usizeValue destination) (usizeValue 0) = .ok (.boolean false) ∧
      IntegerOps.binary .BitAnd (usizeValue source) (usizeValue 0) = .ok (.scalar (ScalarInt.ofUInt64 0)) ∧
      IntegerOps.binary .BitAnd (usizeValue destination) (usizeValue 0) = .ok (.scalar (ScalarInt.ofUInt64 0)) := by
  let source := base + offset
  let destination := source + n
  have initialFits : base.toNat + offset.toNat < 18446744073709551616 := by omega
  have sourceNat : source.toNat = base.toNat + offset.toNat := by simp [source, UInt64.toNat_add, Nat.mod_eq_of_lt initialFits]
  have nextFits : source.toNat + n.toNat < 18446744073709551616 := by omega
  have destinationNat : destination.toNat = source.toNat + n.toNat := by simp [destination, UInt64.toNat_add, Nat.mod_eq_of_lt nextFits]
  have sourceNonzero : source ≠ 0 := by
    intro zero
    have zeroNat := congrArg UInt64.toNat zero
    change source.toNat = 0 at zeroNat
    omega
  have destinationNonzero := source_nonzero_destination_nonzero source n nextFits sourceNonzero
  have nPositive : 0 < n.toNat := by
    by_cases zero : n.toNat = 0
    · exact False.elim (nonzero (UInt64.toNat_inj.mp zero))
    · omega
  refine ⟨sourceNonzero, destinationNonzero, usize_one_mul n,
    adjacent_subtraction source n nextFits, ?_, ?_, ?_, ?_, usize_bitand_zero source, usize_bitand_zero destination⟩
  · rw [usize_lt]
    have ordered : source < destination := UInt64.lt_iff_toNat_lt.mpr (by omega)
    exact congrArg (fun bit => (Except.ok (IntegerResult.boolean bit) : Except IntegerOpError IntegerResult)) (decide_eq_true ordered)
  · rw [usize_ge]
    simp
  · rw [ScalarArithmetic.usize_eq]
    exact congrArg (fun bit => (Except.ok (IntegerResult.boolean bit) : Except IntegerOpError IntegerResult))
      (Bool.eq_false_iff.2 (fun trueEq => sourceNonzero (beq_iff_eq.mp trueEq)))
  · rw [ScalarArithmetic.usize_eq]
    exact congrArg (fun bit => (Except.ok (IntegerResult.boolean bit) : Except IntegerOpError IntegerResult))
      (Bool.eq_false_iff.2 (fun trueEq => destinationNonzero (beq_iff_eq.mp trueEq)))

theorem usize_sizeof_guard : IntegerOps.binary .Eq (usizeValue 8) (usizeValue 4) = .ok (.boolean false) := by decide +kernel

theorem alignment_one_mask :
    IntegerOps.binary .SubWithOverflow (usizeValue 1) (usizeValue 1) = .ok (.withOverflow (ScalarInt.ofUInt64 0) false) := by decide +kernel

theorem u32_one_equals_one : IntegerOps.binary .Eq
    ⟨ScalarInt.ofUInt32 1, ⟨Size.ofBytes 4,.u32⟩⟩
    ⟨ScalarInt.ofUInt32 1, ⟨Size.ofBytes 4,.u32⟩⟩ = .ok (.boolean true) := by decide +kernel

theorem scalar_bool_not [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov State Choice) (choice : Choice)
    (layout boolLayout : LocalLayout) (value : Bool)
    (classification : hooks.classify choice layout.ty = pure .boolean)
    (resultLayout : hooks.boolLayout choice = pure boolLayout) :
    ScalarOps.unary hooks choice .Not (ScalarOperations.boolImmediate value layout) =
      pure (ScalarOperations.boolImmediate (!value) boolLayout : RvalueImmTy Prov) := by
  have scalar := ScalarOperations.bool_scalar_roundtrip (Prov := Prov) value
  simp only [ScalarOperations.boolImmediate]
  funext state
  unfold ScalarOps.unary
  simp_scalar_dispatch

def u32OneImmediate (layout : LocalLayout) : RvalueImmTy Prov :=
  ⟨.scalar (.fromScalarInt (.ofUInt32 1)), layout⟩

theorem scalar_u32_one_eq [PointerProvenance Prov]
    (hooks : ScalarOpsHooks Prov State Choice) (choice : Choice)
    (layout boolLayout : LocalLayout)
    (classification : hooks.classify choice layout.ty = pure (.integer .u32))
    (resultLayout : hooks.boolLayout choice = pure boolLayout)
    (width : layout.layout.size = Size.ofBytes 4) :
    ScalarOps.binary hooks choice .Eq (u32OneImmediate layout) (u32OneImmediate layout) =
      pure (ScalarOperations.boolImmediate true boolLayout : RvalueImmTy Prov) := by
  have operation := u32_one_equals_one
  simp only [ScalarInt.ofUInt32] at operation
  simp only [u32OneImmediate, ScalarInt.ofUInt32, ScalarOperations.boolImmediate]
  funext state
  simp_scalar_dispatch

private theorem scalar_integer_binary_values
    (hooks : ScalarOpsHooks Provenance State Choice) (choice : Choice)
    (layout : LocalLayout) (op : BinOp) (leftScalar rightScalar : Scalar Provenance)
    (left right : UInt64)
    (classification : hooks.classify choice layout.ty = pure (.integer .usize))
    (width : layout.layout.size = Size.ofBytes 8)
    (leftValue : leftScalar.toScalarInt = .ok (ScalarInt.ofUInt64 left))
    (rightValue : rightScalar.toScalarInt = .ok (ScalarInt.ofUInt64 right)) :
    ScalarOps.binary hooks choice op ⟨.scalar leftScalar, layout⟩ ⟨.scalar rightScalar, layout⟩ =
      ScalarOps.binary hooks choice op (ScalarOperations.usizeImmediate left layout) (ScalarOperations.usizeImmediate right layout) := by
  unfold ScalarOps.binary
  unfold_copy ".Miri.Interpreter.ScalarOps.toInteger"
  unfold_copy ".Miri.Interpreter.ScalarOps.toScalar"
  unfold_copy ".Miri.Interpreter.ScalarOps.liftResult"
  unfold_copy ".Miri.Interpreter.ScalarOps.assertSameType"
  funext state
  have fromInt (n : UInt64) : (Scalar.fromScalarInt (ScalarInt.ofUInt64 n) : Scalar Provenance).toScalarInt = .ok (ScalarInt.ofUInt64 n) := rfl
  simp only [classification, ScalarOperations.usizeImmediate, Immediate.toScalar,
    leftValue, rightValue, fromInt, Except.mapError, Bind.bind, EStateM.bind, Pure.pure, EStateM.pure]

def pointerAsUsize (target : TargetDataLayout) (pointer : Pointer Provenance) (layout : LocalLayout) : RvalueImmTy Provenance :=
  ⟨.scalar (.fromPointer target pointer), layout⟩

theorem scalar_pointer_usize_binary_left
    (hooks : ScalarOpsHooks Provenance State Choice) (choice : Choice)
    (target : TargetDataLayout) (pointer : Pointer Provenance)
    (layout : LocalLayout) (op : BinOp) (right : UInt64)
    (classification : hooks.classify choice layout.ty = pure (.integer .usize))
    (width : layout.layout.size = Size.ofBytes 8)
    (targetWidth : target.pointerWidth = .w64) :
    ScalarOps.binary hooks choice op (pointerAsUsize target pointer layout) (ScalarOperations.usizeImmediate right layout) =
      ScalarOps.binary hooks choice op (ScalarOperations.usizeImmediate pointer.offset.bytes layout) (ScalarOperations.usizeImmediate right layout) := by
  exact scalar_integer_binary_values hooks choice layout op _ _ _ _ classification width
    (pointer_to_scalar_int target pointer targetWidth) rfl

theorem scalar_pointer_usize_binary_pair
    (hooks : ScalarOpsHooks Provenance State Choice) (choice : Choice)
    (target : TargetDataLayout) (left right : Pointer Provenance)
    (layout : LocalLayout) (op : BinOp)
    (classification : hooks.classify choice layout.ty = pure (.integer .usize))
    (width : layout.layout.size = Size.ofBytes 8)
    (targetWidth : target.pointerWidth = .w64) :
    ScalarOps.binary hooks choice op (pointerAsUsize target left layout) (pointerAsUsize target right layout) =
      ScalarOps.binary hooks choice op (ScalarOperations.usizeImmediate left.offset.bytes layout) (ScalarOperations.usizeImmediate right.offset.bytes layout) := by
  exact scalar_integer_binary_values hooks choice layout op _ _ _ _ classification width
    (pointer_to_scalar_int target left targetWidth) (pointer_to_scalar_int target right targetWidth)

#print axioms scalar_u64_one_mul
#print axioms integer_cast_word
#print axioms scalar_pointer_usize_binary_pair
#print axioms scalar_bool_not
#print axioms scalar_u32_one_eq
#print axioms count_ones_one
#print axioms cached_byte_slice_checks
#print axioms cached_root_pointer
#print axioms pointer_to_bits
#print axioms scalar_usize_sub_bounded
end DuplicatePrefix.CopyPreconditions

/-! Closed helper data is reflected from production lowering and call resolution,
using the same explicit importer trust boundary as RootBody. The body facts
below identify actual statement operators; they do not replace their execution. -/

open Lean Miri Miri.Input Miri.Interpreter Miri.MIR
namespace DuplicatePrefix.CopyPreconditions.Bodies
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

structure SourceBody where
  sourceId : Nat
  fnInstance : CallInstance
  path : String
  loaded : LoadedBody
  calls : Array (Nat × String)
  deriving Repr, ToExpr

private def readHelpers (path : String) : IO (Except String (Array SourceBody)) := do
  let decoded ← Input.decodeFile path
  let .ok decoded := decoded | return .error "copy helper input decoding failed"
  return do
    let program ← Input.lowerProgram decoded.document
    let prepared ← CallResolution.prepare program
    let mut rows := #[]
    for sourceId in #[27, 28, 32, 33, 34, 36, 37, 38, 39, 40, 41, 42, 44, 50, 54, 13, 26, 5] do
      let some candidate := prepared.bodies.find? (·.sourceInstanceId == sourceId)
        | throw s!"missing source helper instance {sourceId}"
      let some source := prepared.program.input.instances.find? (·.id == sourceId)
        | throw "missing helper source instance"
      let some path := source.defPath | throw "helper source has no def-path"
      let loaded ← CallResolution.loadedBodyOfInstance prepared candidate.fnInstance
      let mut calls := #[]
      for block in [:loaded.body.basicBlocks.size] do
        if let some basic := loaded.body.basicBlocks[block]? then
          if let .Call .. := basic.terminator.kind then
            let resolution ← CallResolution.atSite prepared ⟨loaded.identity.index, block⟩
            let some callee := prepared.program.input.instances.find? (·.id == resolution.sourceInstanceId)
              | throw "missing helper callee instance"
            let some target := callee.defPath | throw "helper callee has no def-path"
            calls := calls.push (block, target)
      rows := rows.push ⟨sourceId, candidate.fnInstance, path, loaded, calls⟩
    return rows

syntax "reflect_copy_helpers " str " as " ident : command
open Lean Elab Command in
elab_rules : command
  | `(reflect_copy_helpers $path:str as $name:ident) => do
    let result ← liftIO <| readHelpers path.getString
    let .ok rows := result | throwError "copy helper reflection failed: {reprStr result}"
    let expression ← liftTermElabM <| pure (toExpr rows)
    liftCoreM <| addDecl <| .defnDecl {
      name := (← getCurrNamespace) ++ name.getId
      levelParams := []
      type := mkApp (mkConst ``Array [Level.zero]) (mkConst ``SourceBody)
      value := expression
      hints := .regular 0
      safety := .safe }

reflect_copy_helpers "examples/duplicate_prefix/input.json" as reflected

theorem source_count : reflected.size = 18 := by rfl

noncomputable section

noncomputable def row (index : Fin 18) : SourceBody := reflected[index.val]'(by rw [source_count]; exact index.isLt)
noncomputable def alignedNotNull : SourceBody := row 0
noncomputable def nonoverlapRuntime : SourceBody := row 4
noncomputable def nullRuntime : SourceBody := row 6
noncomputable def checkedMul : SourceBody := row 8
noncomputable def absDiff : SourceBody := row 9
noncomputable def alignedTo : SourceBody := row 10
noncomputable def overflowingMul : SourceBody := row 12
noncomputable def powerOfTwo : SourceBody := row 13
noncomputable def countOnes : SourceBody := row 14
noncomputable def checkLanguage : SourceBody := row 15
noncomputable def languageRuntime : SourceBody := row 16
noncomputable def copyWrapper : SourceBody := row 17

def statementKindAt (body : MIR.Body) (block statement : Nat) : Option StatementKind :=
  (body.basicBlocks[block]?).bind (fun bb => (bb.statements[statement]?).map Statement.kind)

def binaryAt (body : LoadedBody) (block statement : Nat) : Option BinOp := do
  let .Assign _ (.BinaryOp operation _ _) ← statementKindAt body.body block statement | none
  some operation

def unaryAt (body : LoadedBody) (block statement : Nat) : Option UnOp := do
  let .Assign _ (.UnaryOp operation _) ← statementKindAt body.body block statement | none
  some operation

theorem precondition_calls :
    alignedNotNull.calls = #[(0, "core::ub_checks::maybe_is_aligned"),
      (5, "std::ptr::const_ptr::<impl *const T>::is_null")] := by rfl

theorem nonoverlap_calls : nonoverlapRuntime.calls = #[
    (0,"std::ptr::const_ptr::<impl *const T>::addr"),
    (1,"std::ptr::const_ptr::<impl *const T>::addr"),
    (2,"core::num::<impl usize>::checked_mul"),
    (4,"core::num::<impl usize>::abs_diff"),
    (5,"core::panicking::panic_nounwind")] := by rfl

theorem precondition_operators :
    unaryAt alignedNotNull.loaded 6 1 = some .Not ∧
    binaryAt nonoverlapRuntime.loaded 6 6 = some .Ge ∧
    binaryAt nullRuntime.loaded 1 1 = some .Eq ∧
    binaryAt overflowingMul.loaded 0 11 = some .MulWithOverflow ∧
    binaryAt absDiff.loaded 5 6 = some .Lt ∧
    binaryAt absDiff.loaded 6 6 = some .SubWithOverflow ∧
    binaryAt absDiff.loaded 8 6 = some .SubWithOverflow ∧
    binaryAt alignedTo.loaded 5 4 = some .SubWithOverflow ∧
    binaryAt alignedTo.loaded 6 2 = some .BitAnd ∧
    binaryAt alignedTo.loaded 6 5 = some .Eq ∧
    binaryAt powerOfTwo.loaded 1 1 = some .Eq := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

def terminatorKindAt (body : MIR.Body) (block : Nat) : Option TerminatorKind :=
  (body.basicBlocks[block]?).map (fun bb => bb.terminator.kind)

def unaryConstantAt (body : LoadedBody) (block statement : Nat) : Option ConstOperand := do
  let .Assign _ (.UnaryOp _ (.Constant constant)) ← statementKindAt body.body block statement | none
  some constant

def useConstantAt (body : LoadedBody) (block statement : Nat) : Option ConstOperand := do
  let .Assign _ (.Use (.Constant constant) _) ← statementKindAt body.body block statement | none
  some constant

noncomputable def languageTrueConstant : ConstOperand :=
  (unaryConstantAt languageRuntime.loaded 0 0).get (by decide +kernel)
noncomputable def languageFalseConstant : ConstOperand :=
  (useConstantAt checkLanguage.loaded 3 0).get (by decide +kernel)

theorem language_runtime_literal :
    statementKindAt languageRuntime.loaded.body 0 0 =
      some (.Assign ⟨0,#[]⟩ (.UnaryOp .Not (.Constant languageTrueConstant))) ∧
    languageTrueConstant.value = .Val (.Scalar (.Int 1 1)) 0 ∧
    terminatorKindAt languageRuntime.loaded.body 0 = some .Return := by
  exact ⟨rfl,rfl,rfl⟩

theorem language_parent_false_literal :
    statementKindAt checkLanguage.loaded.body 3 0 =
      some (.Assign ⟨0,#[]⟩ (.Use (.Constant languageFalseConstant) .Yes)) ∧
    languageFalseConstant.value = .Val (.Scalar (.Int 0 1)) 0 := by
  exact ⟨rfl,rfl⟩

theorem language_guard_calls : checkLanguage.calls = #[(0,"core::ub_checks::check_language_ub::runtime")] ∧
    copyWrapper.calls = #[(0,"core::ub_checks::check_language_ub"), (2,"std::mem::size_of"),
      (3,"std::mem::align_of"), (4,"std::ptr::copy_nonoverlapping::precondition_check")] := by
  exact ⟨rfl,rfl⟩

theorem language_guard_branches :
    terminatorKindAt checkLanguage.loaded.body 1 = some (.SwitchInt (.Move ⟨1,#[]⟩) ⟨#[.Case 0 3],2⟩) ∧
    terminatorKindAt checkLanguage.loaded.body 3 = some (.Goto 4 #[]) ∧
    terminatorKindAt checkLanguage.loaded.body 4 = some .Return ∧
    terminatorKindAt copyWrapper.loaded.body 1 = some (.SwitchInt (.Move ⟨5,#[]⟩) ⟨#[.Case 0 6],2⟩) ∧
    terminatorKindAt copyWrapper.loaded.body 6 = some (.Goto 7 #[]) ∧
    copyWrapper.loaded = RootBody.reflected.copyHelper := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms language_runtime_literal
#print axioms language_parent_false_literal
#print axioms language_guard_branches
#print axioms language_guard_calls
#print axioms precondition_operators
end
end DuplicatePrefix.CopyPreconditions.Bodies
