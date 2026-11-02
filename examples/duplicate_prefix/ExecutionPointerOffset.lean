import duplicate_prefix.PointerOffsetBounds
import Miri.Interpreter.ExecutionScalar

/-! Offset arithmetic in the scalar hooks actually assembled by
ExecutionMachine, separate from the PointerMachine adapter. -/
namespace DuplicatePrefix.ExecutionPointerOffset
open Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

open Lean Elab Tactic in
elab "simp_execution_integer" : tactic => do
  let env ← getEnv
  let names ← ([".ExecutionScalar.integer", ".ExecutionScalar.lift"] : List String).mapM
    fun (suffix : String) => do
      let found := env.constants.toList.filterMap fun (name, _) =>
        if name.toString.endsWith suffix then some (mkIdent name) else none
      match found with
      | [name] => pure name
      | _ => throwError "expected exact source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp_all [ExecutionScalar.integerBinary, ExecutionScalar.finish,
    ScalarOperations.usizeImmediate, Immediate.toScalar, Scalar.fromScalarInt,
    Scalar.toScalarInt, Scalar.tryToScalarInt, ScalarInt.toBits, ScalarInt.size,
    ScalarInt.ofUInt64, bind, EStateM.bind, pure, EStateM.pure, Except.pure,
    Except.bind, Except.mapError, $[$names:ident],*]))

theorem integer_mul_one
    (queries : ExecutionScalar.Leaves (MachineHooks.State K User) Choice)
    (choice : Choice) (layout overflowLayout : LocalLayout) (count : UInt64)
    (classification : queries.classify choice layout.ty = pure (.integer .usize))
    (overflowQuery : queries.overflowLayout choice layout = pure overflowLayout)
    (width : layout.layout.size = Size.ofBytes 8) :
    ExecutionScalar.integerBinary queries choice .MulWithOverflow
      (ScalarOperations.usizeImmediate count layout)
      (ScalarOperations.usizeImmediate 1 layout) =
      pure (⟨.scalarPair (.fromScalarInt (.ofUInt64 count)) (.fromBool false),overflowLayout⟩ :
        RvalueImmTy Provenance) := by
  have operation := ScalarArithmetic.usize_mul_one count
  simp only [ScalarArithmetic.usizeValue, ScalarInt.ofUInt64] at operation
  funext state
  simp_execution_integer

theorem checked_bounds_cached
    (arithmetic : PointerArithmetic)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (present : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    checkPtrAccessSigned arithmetic
      (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset)))
      (Int64.ofInt (Int.ofNat count.toNat)) .inboundsPointerArithmetic
      (fun _ _ => .ok ⟨id,Size.ofBytes offset,ProvenanceExtra.concrete tag⟩)
      memory.getAllocInfo = .ok () := by
  have signed : (Int64.ofInt (Int.ofNat count.toNat)).toInt = (count.toNat : Int) :=
    Int64.toInt_ofInt_of_le (Int.le_trans (by decide) (Int.natCast_nonneg _)) (Int.ofNat_lt.mpr fits)
  have lookup := MemoryCopyBridge.live_alloc_info memory id entry present
  have access := PointerAccess.dereference_ok arithmetic
    (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset)))
    count.toNat .inboundsPointerArithmetic
    (fun _ _ => .ok ⟨id,Size.ofBytes offset,ProvenanceExtra.concrete tag⟩)
    memory.getAllocInfo ⟨id,Size.ofBytes offset,ProvenanceExtra.concrete tag⟩
    ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩
    positive fits rfl lookup (by simp) bounds
  unfold checkPtrAccessSigned
  rw [signed]
  change checkAndDerefPtr arithmetic _ (count.toNat : Int) _ _ _ = _ at access
  rw [access]
  rfl

theorem signed_word (count : UInt64) :
    (Int64.ofInt (Int.ofNat count.toNat)).toUInt64 = count := by
  change (Int64.ofInt (count.toNat : Int)).toUInt64 = count
  rw [Int64.ofInt_eq_ofNat]
  change UInt64.ofNat count.toNat = count
  exact UInt64.ofNat_toNat

open Lean Elab Tactic in
elab "simp_execution_pointer" : tactic => do
  let env ← getEnv
  let names ← ([".ExecutionScalar.scalar", ".ExecutionScalar.lift", ".ExecutionScalar.machineAction"] : List String).mapM
    fun (suffix : String) => do
      let found := env.constants.toList.filterMap fun (name, _) =>
        if name.toString.endsWith suffix then some (mkIdent name) else none
      match found with
      | [name] => pure name
      | _ => throwError "expected exact source helper {suffix}"
  let names := names.toArray
  evalTactic (← `(tactic| simp (config := {maxSteps := 1000000}) [*, ExecutionScalar.hooks,
    PointerDispatch.pointerImmediate, ScalarOperations.usizeImmediate, Immediate.toScalar,
    Immediate.toScalarPair, Pointer.withOptionalProvenance, Pointer.mapProvenance, Pointer.new,
    Pointer.wrappingSignedOffset, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, pure, EStateM.pure, Except.bind, Except.pure,
    Except.mapError, $[$names:ident],*]))

theorem pointer_binary_cached
    (access : PlaceMachine.AccessConfig K (ValidityMachine.UserState User))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control User))
    (arithmetic : PointerArithmetic)
    (queries : ExecutionScalar.Leaves (MachineHooks.State K (ValidityMachine.UserState User)) Choice)
    (isRaw : Choice → TyId → MachineHooks.M K (ValidityMachine.UserState User) Bool)
    (usize : Choice → MachineHooks.M K (ValidityMachine.UserState User) LocalLayout)
    (pointee : Choice → TyId → MachineHooks.M K (ValidityMachine.UserState User) LocalLayout)
    (dereference : Choice → OpTy Provenance → MachineHooks.M K (ValidityMachine.UserState User) (MPlaceTy Provenance))
    (floats : FloatOpsHooks Provenance (MachineHooks.State K (ValidityMachine.UserState User)) Choice)
    (choice : Choice) (state : MachineHooks.State K (ValidityMachine.UserState User))
    (pointerLayout countLayout elementLayout overflowLayout : LocalLayout)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (pointeeQuery : pointee choice pointerLayout.ty = pure elementLayout)
    (sized : elementLayout.layout.isSized = true)
    (elementSize : elementLayout.layout.size = Size.ofBytes 1)
    (countSize : countLayout.layout.size = Size.ofBytes 8)
    (classification : queries.classify choice countLayout.ty = pure (.integer .usize))
    (overflowQuery : queries.overflowLayout choice countLayout = pure overflowLayout)
    (unsigned : countLayout.layout.backendRepr.isSigned = .ok false)
    (arithmeticWidth : arithmetic = ⟨Size.ofBytes 8⟩)
    (pointerWidth : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (resolutionWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : 0 < count.toNat) (fits : count.toNat < 2^63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    (ExecutionScalar.hooks queries access arithmetic isRaw usize pointee dereference floats).pointerBinary
      choice .Offset
      (PointerDispatch.pointerImmediate access.runtime.base
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset))) pointerLayout)
      (ScalarOperations.usizeImmediate count countLayout) state =
      .ok (PointerDispatch.pointerImmediate access.runtime.base
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count))) pointerLayout) state := by
  have product := integer_mul_one queries choice countLayout overflowLayout count classification overflowQuery countSize
  have roundtrip := ScalarPointers.pointer_roundtrip access.runtime.base
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))
  have integerSigned := ScalarPointers.scalar_uint64_to_isize (Prov := Provenance) count fits
  have signed : (Int64.ofInt (Int.ofNat count.toNat)).toInt = (count.toNat : Int) :=
    Int64.toInt_ofInt_of_le (Int.le_trans (by decide) (Int.natCast_nonneg _)) (Int.ofNat_lt.mpr fits)
  have nonnegative : ¬ (count.toNat : Int) < 0 := by omega
  have bytesAdd : (Size.ofBytes (base + offset)).bytes + (Size.ofBytes count).bytes = base + offset + count := rfl
  have nonzero : (Int64.ofInt (Int.ofNat count.toNat) == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro eq
    have equality := (beq_iff_eq).mp eq
    have impossible := congrArg Int64.toInt equality
    rw [signed] at impossible
    change (count.toNat : Int) = 0 at impossible
    omega
  have nonzeroEq : Int64.ofInt (Int.ofNat count.toNat) ≠ 0 := by
    intro equality
    have impossible := congrArg Int64.toInt equality
    rw [signed] at impossible
    change (count.toNat : Int) = 0 at impossible
    omega
  rw [Int64.toInt_ofInt] at signed
  change (count.toNat : Int).bmod Int64.size = (count.toNat : Int) at signed
  change Int64.ofInt (count.toNat : Int) ≠ 0 at nonzeroEq
  have resolve := MemoryCopyBridge.typed_resolve_cached pointers state.machine.memory state.machine
    id tag base offset (count.toNat : Int) pointerWidth (by omega) (Int.ofNat_lt.mpr fits) cached
  rw [← resolutionWiring] at resolve
  have checked := checked_bounds_cached arithmetic state.machine.memory id tag base offset count entry
    present positive fits bounds
  rw [arithmeticWidth] at checked
  change checkPtrAccessSigned ⟨Size.ofBytes 8⟩
      {offset := Size.ofBytes (base+offset), provenance := some (Provenance.concrete id tag)}
      (Int64.ofInt (count.toNat : Int)) .inboundsPointerArithmetic
      (fun _ _ => .ok ⟨id, Size.ofBytes offset, ProvenanceExtra.concrete tag⟩)
      state.machine.memory.getAllocInfo = .ok () at checked
  have strideBytes : (Size.ofBytes 1).bytes.toNat = 1 := rfl
  have stride := ScalarPointers.scalar_int_one (Prov := Provenance)
  have overflowFalse := ScalarPointers.scalar_false_bool (Prov := Provenance)
  have word := signed_word count
  change (Int64.ofInt (count.toNat : Int)).toUInt64 = count at word
  have wrap := PointerArithmetic.wrapping_offset_u64
    (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset))) (Size.ofBytes count)
  change (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset))).wrappingOffset
      (Size.ofBytes count) ⟨Size.ofBytes 8⟩ = _ at wrap
  have encoded := ScalarPointers.from_some_pointer access.runtime.base
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count)))
  simp only [Pointer.new, Pointer.withOptionalProvenance,
    ScalarOperations.usizeImmediate] at roundtrip product resolve checked encoded wrap
  dsimp only [ExecutionScalar.hooks, PointerDispatch.pointerImmediate]
  simp_execution_pointer

theorem scalar_binary_pointer
    (hooks : ScalarOpsHooks Provenance State Choice) (choice : Choice)
    (operation : BinOp) (left right : RvalueImmTy Provenance)
    (leftClass : hooks.classify choice left.layout.ty = pure .pointer)
    (rightClass : hooks.classify choice right.layout.ty = pure (.integer .usize)) :
    ScalarOps.binary hooks choice operation left right = hooks.pointerBinary choice operation left right := by
  funext state
  simp only [ScalarOps.binary, leftClass, rightClass, bind, EStateM.bind, pure, EStateM.pure]

#print axioms pointer_binary_cached
#print axioms scalar_binary_pointer
#print axioms integer_mul_one
end DuplicatePrefix.ExecutionPointerOffset
