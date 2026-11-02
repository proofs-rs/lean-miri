import duplicate_prefix.MemoryCopyBridge
import duplicate_prefix.PointerAccess
import duplicate_prefix.PointerDispatch

namespace DuplicatePrefix.PointerOffsetBounds
open Miri.MIR Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter

set_option maxRecDepth 32768
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

theorem resolve_cached {K U : Type}
    (hooks : PointerMachine.Hooks K U) (state : PointerMachine.State K U)
    (id : AllocId) (tag : BorTag) (base offset : UInt64) (size : Int64)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id,base⟩) :
    PointerMachine.ptrGetAlloc hooks
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset))) size state =
      .ok (some (id,Size.ofBytes offset)) state := by
  unfold PointerMachine.ptrGetAlloc
  unfold_internal ".PointerMachine.addresses"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure]
  have resolved := MemoryCopyBridge.ptr_get_alloc_cached state.machine.user.addresses
    id tag base offset size
    { sizeOf := fun id => (state.machine.memory.getAllocInfo id).toOption.map (·.size)
      isLive := fun id => some (state.machine.memory.isAllocLive id) }
    hooks.arithmetic width cached
  simp only [resolved]
  rfl

private theorem signed_access_stage {K U : Type}
    (hooks : PointerMachine.Hooks K U) (state : PointerMachine.State K U)
    (id : AllocId) (tag : BorTag) (base offset : UInt64) (size : Int64)
    (nonzero : (size == 0) = false)
    (resolved : PointerMachine.ptrGetAlloc hooks
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset))) size state =
      .ok (some (id,Size.ofBytes offset)) state)
    (access : checkPtrAccessSigned hooks.arithmetic
      (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset))) size
      .inboundsPointerArithmetic
      (fun _ _ => .ok ⟨id,Size.ofBytes offset,Provenance.concrete id tag⟩)
      state.machine.memory.getAllocInfo = .ok ()) :
    PointerMachine.checkAccessSigned hooks
      (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset)))
      size .inboundsPointerArithmetic state = .ok () state := by
  unfold PointerMachine.checkAccessSigned
  simp only [nonzero, Bool.false_eq_true, ↓reduceIte, Pointer.new]
  simp only [Pointer.new] at resolved access
  simp only [bind, EStateM.bind, resolved, get, getThe, MonadStateOf.get, EStateM.get,
    pure, EStateM.pure, Option.getD_some]
  erw [access]
  rfl

theorem signed_access_cached {K U : Type}
    (hooks : PointerMachine.Hooks K U)
    (state : PointerMachine.State K U)
    (id : AllocId) (tag : BorTag) (base offset : UInt64)
    (count : UInt64) (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : 0 < count.toNat) (fits : count.toNat < 2 ^ 63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    PointerMachine.checkAccessSigned hooks
      (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base + offset)))
      (Int64.ofInt (Int.ofNat count.toNat)) .inboundsPointerArithmetic state = .ok () state := by
  have signed : (Int64.ofInt (Int.ofNat count.toNat)).toInt = (count.toNat : Int) :=
    Int64.toInt_ofInt_of_le (Int.le_trans (by decide) (Int.ofNat_nonneg _)) (Int.ofNat_lt.mpr fits)
  have nonzero : (Int64.ofInt (Int.ofNat count.toNat) == 0) = false := by
    apply Bool.eq_false_iff.mpr
    intro eq
    have equality := (beq_iff_eq).mp eq
    have := congrArg Int64.toInt equality
    simp only [signed] at this
    change (count.toNat : Int) = 0 at this
    omega
  have lookup := MemoryCopyBridge.live_alloc_info state.machine.memory id entry present
  have access := PointerAccess.dereference_ok hooks.arithmetic
    (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base + offset)))
    count.toNat .inboundsPointerArithmetic
    (fun _ _ => .ok ⟨id,Size.ofBytes offset, Provenance.concrete id tag⟩)
    state.machine.memory.getAllocInfo
    ⟨id,Size.ofBytes offset, Provenance.concrete id tag⟩
    ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩
    positive fits rfl lookup (by simp) bounds
  have pureAccess : checkPtrAccessSigned hooks.arithmetic
      (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset)))
      (Int64.ofInt (Int.ofNat count.toNat)) .inboundsPointerArithmetic
      (fun _ _ => .ok ⟨id,Size.ofBytes offset,Provenance.concrete id tag⟩)
      state.machine.memory.getAllocInfo = .ok () := by
    unfold checkPtrAccessSigned
    rw [signed]
    change checkAndDerefPtr hooks.arithmetic
      (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset)))
      (count.toNat : Int) .inboundsPointerArithmetic _ _ = _ at access
    rw [access]
    rfl
  exact signed_access_stage hooks state id tag base offset _ nonzero
    (resolve_cached hooks state id tag base offset _ width cached) pureAccess

theorem positive_offset_cached {K U : Type}
    (hooks : PointerMachine.Hooks K U)
    (state : PointerMachine.State K U)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : 0 < count.toNat) (fits : count.toNat < 2 ^ 63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    PointerMachine.offsetInbounds hooks
      (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset)))
      (Int64.ofInt (Int.ofNat count.toNat)) state =
      .ok (Pointer.new (some (Provenance.concrete id tag))
        (Size.ofBytes (base+offset+count))) state := by
  have access := signed_access_cached hooks state id tag base offset count entry
    width cached present positive fits bounds
  have signedWord : (Int64.ofInt (Int.ofNat count.toNat)).toUInt64 = count := by
    change (Int64.ofInt (count.toNat : Int)).toUInt64 = count
    rw [Int64.ofInt_eq_ofNat]
    change UInt64.ofNat count.toNat = count
    exact UInt64.ofNat_toNat
  have wrap := DuplicatePrefix.PointerArithmetic.wrapping_offset_u64
    (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset)))
    (Size.ofBytes count)
  unfold PointerMachine.offsetInbounds
  simp only [bind, EStateM.bind, access]
  unfold Pointer.wrappingSignedOffset
  rw [signedWord, width]
  erw [wrap]
  rfl

theorem offset_dispatch_cached {K U Choice : Type}
    (hooks : PointerMachine.Hooks K U)
    (target : TargetDataLayout)
    (ops : ScalarOpsHooks Provenance (PointerMachine.State K U) Choice)
    (isRaw : Choice → TyId → PointerMachine.M K U Bool)
    (usize : Choice → PointerMachine.M K U LocalLayout)
    (pointee : Choice → TyId → PointerMachine.M K U LocalLayout)
    (choice : Choice) (state : PointerMachine.State K U)
    (id : AllocId) (tag : BorTag) (base offset count : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (pointerLayout countLayout elementLayout overflowLayout : LocalLayout)
    (pointeeQuery : pointee choice pointerLayout.ty = pure elementLayout)
    (sized : elementLayout.layout.isSized = true)
    (elementSize : elementLayout.layout.size = Size.ofBytes 1)
    (countSize : countLayout.layout.size = Size.ofBytes 8)
    (classification : ops.classify choice countLayout.ty = pure (.integer .usize))
    (overflowQuery : ops.overflowLayout choice countLayout = pure overflowLayout)
    (unsigned : countLayout.layout.backendRepr.isSigned = .ok false)
    (width : hooks.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id,base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (positive : 0 < count.toNat) (fits : count.toNat < 2 ^ 63)
    (bounds : offset.toNat + count.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    PointerMachine.binary hooks target ops isRaw usize pointee choice .Offset
      (PointerDispatch.pointerImmediate target
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset))) pointerLayout)
      (ScalarOperations.usizeImmediate count countLayout) state =
      .ok (PointerDispatch.pointerImmediate target
        (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count))) pointerLayout)
        state := by
  rw [PointerDispatch.offset_reduction hooks target ops isRaw usize pointee choice
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset)))
    pointerLayout countLayout elementLayout overflowLayout count pointeeQuery sized
    elementSize countSize (congrArg (·.pointerSize) width) classification overflowQuery unsigned fits]
  have addition := positive_offset_cached hooks state id tag base offset count entry
    width cached present positive fits bounds
  change PointerMachine.offsetInbounds hooks
    (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset))).withOptionalProvenance
    (Int64.ofInt (Int.ofNat count.toNat)) state = _ at addition
  simp only [bind, EStateM.bind, addition]
  rw [show Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base+offset+count)) =
      (Pointer.new (Provenance.concrete id tag) (Size.ofBytes (base+offset+count))).withOptionalProvenance
      from rfl, ScalarPointers.from_some_pointer]
  rfl

#print axioms offset_dispatch_cached

#print axioms signed_access_cached
#print axioms positive_offset_cached

end DuplicatePrefix.PointerOffsetBounds
