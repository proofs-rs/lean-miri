import Miri.Interpreter.MemoryOperand

open Miri.ABI Miri.Memory Miri.Interpreter

private structure Hooks where
  events : Array String := #[]

private def machineOk (state : Hooks) (value : α) : MachineHookResult Hooks α :=
  ⟨state, .ok value⟩

private def globalHooks : GlobalAllocationHooks CtfeProvenance Unit Unit Hooks := {
  synchronizeMemory := fun _ state => state
  evaluateStaticInitializer := fun memory state _ => ⟨memory, state, .error "unused"⟩
  beforeAccessGlobal := fun memory state _ _ _ _ => ⟨memory, state, .ok ()⟩
  adjustGlobalAllocation := fun memory state _ allocation => ⟨memory, state, .ok (.borrowed allocation)⟩
}

private def accessHooks : AllocationAccessHooks CtfeProvenance Unit Unit Hooks Unit := {
  resolvePointer := fun _ state pointer _ =>
    match pointer.provenance with
    | some provenance => ⟨state, .ok (.ok ⟨provenance.allocId, pointer.offset, ()⟩)⟩
    | none => ⟨state, .ok (.error pointer.offset.bytes)⟩
  beforeAllocationAccess := fun state _ => machineOk state ()
  beforeMemoryRead := fun state extra _ _ _ _ => ⟨state, extra, .ok ()⟩
  beforeMemoryWrite := fun state extra _ _ _ _ => ⟨state, extra, .ok ()⟩
}

private def dynamicLayout : DynamicLayoutResolver CtfeProvenance Unit Unit Hooks :=
  fun memory hooks _ => ⟨memory, hooks, .ok none⟩

private def runtime : RuntimeTargetDataLayout :=
  { RuntimeTargetDataLayout.default with base := ⟨.little, .w64⟩ }

private def sz (value : Nat) : Size := Size.ofBytes (UInt64.ofNat value)
private def range (start finish : Nat) : AllocRange := allocRange (sz start) (sz (finish - start))

private def requireScalar (value : Nat) (size : Size) : IO (Scalar CtfeProvenance) := do
  match Scalar.fromUInt (BitVec.ofNat 128 value) size with
  | .ok scalar => pure scalar
  | .error _ => throw (IO.userError "test scalar construction failed")

private def requireAlloc (result : EStateM.Result AllocError
    (Allocation CtfeProvenance Unit) Unit) : IO (Allocation CtfeProvenance Unit) := do
  match result with
  | .ok () allocation => pure allocation
  | .error _ _ => throw (IO.userError "test allocation setup failed")

private def fullRange (size : Size) : IO WrappingRange := do
  match WrappingRange.full size with
  | .ok value => pure value
  | .error _ => throw (IO.userError "test ABI range construction failed")

private def initialized (primitive : Miri.ABI.Primitive) (size : Size) : IO Miri.ABI.Scalar := do
  return .Initialized (value := primitive) (validRange := ← fullRange size)

private def id7 : IO AllocId := do
  match AllocId.ofUInt64 7 with
  | some value => pure value
  | none => throw (IO.userError "test ID construction failed")

private def provenanceFor (id : AllocId) : IO CtfeProvenance := do
  match CtfeProvenance.fromAllocId id with
  | .ok value => pure value
  | .error _ => throw (IO.userError "test provenance construction failed")

private def makeMemory : IO
    (MemoryState CtfeProvenance Unit Unit × Pointer (Option CtfeProvenance)) := do
  let id ← id7
  let prov ← provenanceFor id
  let mut allocation ← match Allocation.fromBytes (Array.replicate 24 0) Align.ONE .Mut with
    | .ok value => pure value
    | .error _ => throw (IO.userError "test allocation construction failed")
  allocation ← requireAlloc <| Allocation.writeScalar runtime.base (range 0 8)
      (← requireScalar 0x123456789abcdef0 (sz 8)) allocation
  allocation ← requireAlloc <| Allocation.writeScalar runtime.base (range 8 16)
      (Scalar.fromPointer runtime.base (Pointer.new prov (sz 0x1234))) allocation
  allocation ← requireAlloc <| Allocation.writeScalar runtime.base (range 16 24)
      (← requireScalar 99 (sz 8)) allocation
  let empty : MemoryState CtfeProvenance Unit Unit := MemoryState.empty
  let issued := MemoryState.setIssuedIds empty #[id]
  let state : MemoryState CtfeProvenance Unit Unit := {
    issued with live := #[(id, ⟨.stack, allocation⟩)] }
  pure (state, Pointer.new (some prov) Size.ZERO)

private def showScalar (value : Scalar CtfeProvenance) : IO String := do
  if value.isPointer then
    let ptr ← match value.toPointer runtime.base with
      | .ok ptr => pure ptr
      | .error _ => throw (IO.userError "test pointer decode failed")
    return s!"p{value.size.bytes.toNat}:{ptr.offset.bytes.toNat}"
  else
    let int ← match value.toScalarInt with
      | .ok int => pure int
      | .error _ => throw (IO.userError "test integer decode failed")
    return s!"i{int.size.bytes.toNat}:{int.data.toNat}"

private def showImmediate (value : Immediate CtfeProvenance) : IO String := do
  match value with
  | .uninit => pure "uninit"
  | .scalar scalar => showScalar scalar
  | .scalarPair first second => return s!"pair({← showScalar first}, {← showScalar second})"

private def emitRead (tag : String) (memory : MemoryState CtfeProvenance Unit Unit)
    (pointer : Pointer (Option CtfeProvenance)) (layout : MemoryOperandLayout) : IO Unit := do
  let place : MemoryOperandPlace CtfeProvenance :=
    ⟨⟨pointer, .none, none⟩, layout⟩
  let result := readImmediateFromMplaceRaw memory {} place runtime false none
      globalHooks accessHooks dynamicLayout
  match result.outcome with
  | .error (.allocation (.invalidUninitBytes (some bad))) =>
      let finish ← match bad.bad.endExclusive with
        | .ok value => pure value
        | .error _ => throw (IO.userError "error range end failed")
      IO.println s!"R {tag} uninit:{bad.bad.start.bytes.toNat}:{finish.bytes.toNat}"
  | .error (.allocation (.readPointerAsInt _)) => IO.println s!"R {tag} pointer-as-int"
  | .error (.allocation (.readPartialPointer offset)) =>
      IO.println s!"R {tag} partial-pointer:{offset.bytes.toNat}"
  | .error error => IO.println s!"R {tag} other:{repr error}"
  | .ok none => IO.println s!"R {tag} none"
  | .ok (some value) => IO.println s!"R {tag} {← showImmediate value.value}"

private def rawResult (memory : MemoryState CtfeProvenance Unit Unit)
    (operand : Operand CtfeProvenance)
    (layout : MemoryOperandLayout) : IO String := do
  let result := readImmediateRaw memory {} operand layout runtime false none
      globalHooks accessHooks dynamicLayout
  match result.outcome with
  | .error error => return s!"error:{repr error}"
  | .ok (.place _) => return "place"
  | .ok (.immediate value) => return s!"immediate:{← showImmediate value.value}"

def main : IO Unit := do
  let (memory, pointer) ← makeMemory
  let i64 ← initialized (.Int .I64 false) (sz 8)
  let ptr ← initialized (.Pointer AddressSpace.ZERO) (sz 8)
  let union := Miri.ABI.Scalar.Union (value := .Int .I64 false)
  let intLayout : MemoryOperandLayout := ⟨sz 8, Align.ONE, .Scalar i64, none⟩
  let ptrLayout : MemoryOperandLayout := ⟨sz 8, Align.ONE, .Scalar ptr, none⟩
  let pairLayout : MemoryOperandLayout := ⟨sz 16, Align.ONE,
    .ScalarPair (a := i64) (b := ptr) (bOffset := sz 8), none⟩
  let unionLayout : MemoryOperandLayout := ⟨sz 8, Align.ONE, .Scalar union, none⟩
  let memoryLayout : MemoryOperandLayout := ⟨sz 8, Align.ONE, .Memory (sized := true), none⟩
  let unsizedLayout : MemoryOperandLayout := ⟨Size.ZERO, Align.ONE, .Memory (sized := false), none⟩
  let zstLayout : MemoryOperandLayout := ⟨Size.ZERO, Align.ONE, .Memory (sized := true), none⟩
  emitRead "scalar" memory pointer intLayout
  let pointerAt8 := Pointer.new pointer.provenance (sz 8)
  emitRead "pointer" memory pointerAt8 ptrLayout
  emitRead "pointer_as_integer" memory pointerAt8 intLayout
  emitRead "pair" memory pointer pairLayout
  emitRead "union" memory pointer unionLayout
  emitRead "memory" memory pointer memoryLayout
  emitRead "unsized" memory pointer unsizedLayout
  IO.println s!"O memory_fallback {← rawResult memory (.indirect ⟨pointer, .none, none⟩) memoryLayout}"
  IO.println s!"O indirect_scalar {← rawResult memory (.indirect ⟨pointer, .none, none⟩) intLayout}"
  let u8 ← initialized (.Int .I8 false) (sz 1)
  let immediate := Immediate.scalar (← requireScalar 7 (sz 1))
  let u8Layout : MemoryOperandLayout := ⟨sz 1, Align.ONE, .Scalar u8, none⟩
  IO.println s!"O already_immediate {← rawResult memory (.immediate immediate) u8Layout}"
  let id ← id7
  let some (_, entry) := memory.live[0]?
    | throw (IO.userError "test allocation is absent")
  let uninitialized ← requireAlloc <| Allocation.writeUninit (range 0 8) (sz 8)
      entry.allocation
  let updatedMemory := { memory with live := #[(id, { entry with allocation := uninitialized })] }
  emitRead "uninitialized" updatedMemory pointer intLayout
  let empty : MemoryState CtfeProvenance Unit Unit := MemoryState.empty
  emitRead "zero_sized_allocation" empty pointer zstLayout

