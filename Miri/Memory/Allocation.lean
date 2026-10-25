import Miri.Memory.NativeBuffer
import Miri.Memory.InitMask
import Miri.Memory.ProvenanceMap
import Miri.Memory.Scalar
import Miri.ABI.Align

/-!
The source-level allocation record and checked read-byte operations from the
pinned `rustc_middle::mir::interpret::allocation` module. The byte backend is
represented by `Array UInt8`; host allocation is an explicit callback at the
fallible constructor boundary.
-/

namespace Miri.Memory

open Miri.ABI

inductive Mutability where
  | Not
  | Mut
  deriving DecidableEq, Repr

inductive AllocInit where
  | Uninit
  | Zero
  deriving DecidableEq, Repr

structure BadBytesAccess where
  access : AllocRange
  bad : AllocRange
  deriving DecidableEq, Repr

inductive AllocError where
  | readPointerAsInt (info : Option BadBytesAccess)
  | readPartialPointer (offset : Size)
  | invalidUninitBytes (info : Option BadBytesAccess)
  | memory (reason : MemoryError)
  | provenance (reason : ProvenanceMapError)
  | alignment (reason : AlignError)
  | storageLengthOverflow (length : Nat)
  | storageLengthMismatch (requested : Size) (actual : Nat)
  | storageBackendNotZeroed (index : Nat) (value : UInt8)
  | outOfBounds (range : AllocRange) (allocationSize : Size)
  | invalidSliceEndpoints (start finish available : Nat)
  | nonEmptyProvenanceWithoutEntry
  | readOnlyAllocation
  | pointerSizeMismatch (scalarSize pointerSize : Size)
  | scalar (reason : ScalarError)
  | scalarBytesTooWide (size : Size)
  | pointerBitsDoNotFitOffset (bits : U128)
  | scalarPointerNotTargetSized (scalarSize targetSize : Size)
  | copyRangesOverlap
  | repeatedCopyRequiresNonoverlapping
  | singleByteZeroCountCopy
  | allocationHasByteFragmentProvenance
  | nativeWriteRangeOutOfBounds (range : AllocRange) (allocationSize : Size)
  | hostMemoryExhausted
  deriving DecidableEq, Repr

inductive AllocationAdjustError (CallbackError : Type) where
  | allocation (reason : AllocError)
  | byteConversion (reason : CallbackError)
  | pointerAdjustment (reason : CallbackError)
  deriving DecidableEq, Repr

private def provenanceErrorText : ProvenanceMapError → String
  | .memory reason => toString reason
  | .pointerSizeZero => "zero-sized target pointer"
  | .unsortedOrDuplicateKeys => "unsorted or duplicate provenance keys"
  | .readPartialPointer offset => s!"partial pointer at {offset.bytes}"
  | .missingWildcard => "missing wildcard provenance"
  | .pointerSizedProvenanceAtByte offset => s!"pointer-sized provenance at byte {offset.bytes}"
  | .insertOverlapsExistingProvenance => "provenance insertion overlaps an existing pointer"
  | .pointerSizeExceedsFragmentStorage bytes =>
      s!"pointer size {bytes} exceeds the supported fragment byte count"
  | .fragmentSliceOutOfBounds start size available =>
      s!"fragment byte slice starts at {start.bytes} with size {size.bytes}, beyond {available} bytes"
  | .copyEntryCountOverflow => "provenance copy entry count exceeds the supported host index range"

instance : ToString ProvenanceMapError where
  toString := provenanceErrorText

instance : ToString AllocError where
  toString
    | .readPointerAsInt _ => "allocation read encountered pointer provenance where bytes were required"
    | .readPartialPointer offset => s!"allocation read encountered a partial pointer at {offset.bytes}"
    | .invalidUninitBytes _ => "allocation read encountered uninitialized bytes"
    | .memory reason => toString reason
    | .provenance reason => s!"provenance-map error: {reason}"
    | .alignment reason => s!"alignment error: {reason}"
    | .storageLengthOverflow length => s!"byte length {length} does not fit in rustc Size"
    | .storageLengthMismatch requested actual =>
        s!"zeroed storage has {actual} bytes, but {requested.bytes} were requested"
    | .storageBackendNotZeroed index value =>
        s!"zeroed-storage backend returned byte {value} at index {index}"
    | .outOfBounds range allocationSize =>
        s!"byte range starting at {range.start.bytes} with length {range.size.bytes} is outside allocation size {allocationSize.bytes}"
    | .invalidSliceEndpoints start finish available =>
        s!"slice [{start}..{finish}] is outside {available} stored bytes"
    | .nonEmptyProvenanceWithoutEntry =>
        "provenance map reported a nonempty overlap without yielding an entry"
    | .readOnlyAllocation => "cannot mutate an immutable allocation"
    | .pointerSizeMismatch scalarSize pointerSize =>
        s!"pointer scalar size {scalarSize.bytes} differs from target pointer size {pointerSize.bytes}"
    | .scalar reason => s!"scalar error: {reason}"
    | .scalarBytesTooWide size => s!"{size.bytes}-byte scalar exceeds the 16-byte integer width"
    | .pointerBitsDoNotFitOffset bits => s!"pointer bits {bits.toNat} do not fit a u64 offset"
    | .scalarPointerNotTargetSized scalarSize targetSize =>
        s!"pointer scalar size {scalarSize.bytes} differs from target pointer size {targetSize.bytes}"
    | .copyRangesOverlap => "nonoverlapping memory copy received overlapping source and destination ranges"
    | .repeatedCopyRequiresNonoverlapping => "repeated memory copies require nonoverlapping mode"
    | .singleByteZeroCountCopy => "single-byte repeated copy asserted a nonzero copy count"
    | .allocationHasByteFragmentProvenance =>
        "CTFE allocation adjustment requires interned pointer-only provenance"
    | .nativeWriteRangeOutOfBounds range allocationSize =>
        s!"native-write range starting at {range.start.bytes} with length {range.size.bytes} is outside allocation size {allocationSize.bytes}"
    | .hostMemoryExhausted => "host allocation failed while creating the rustc allocation"

private def maxU64Nat : Nat := 18446744073709551615

private def checkedAlign (align : Align) : Except AllocError Align := do
  let bytes ← (Align.bytes align).mapError AllocError.alignment
  let normalized ← (Align.fromBytes bytes).mapError AllocError.alignment
  if normalized == align then return align
  throw (.alignment (.tooLarge bytes))

private def sizeForArray (length : Nat) : Except AllocError Size := do
  if length > maxU64Nat then throw (.storageLengthOverflow length)
  let size := Size.ofBytes (UInt64.ofNat length)
  if size.bytes.toNat == length then return size
  throw (.storageLengthOverflow length)

private def pointerSize (layout : TargetDataLayout) : Size :=
  Size.fromBits layout.pointerWidth.bits

private def targetUIntBytes (layout : TargetDataLayout) (size : Size) (bits : U128) :
    Except AllocError (Array UInt8) := do
  if size.bytes > 16 then throw (.scalarBytesTooWide size)
  let count := size.bytes.toNat
  let mut result := #[]
  for index in [:count] do
    let valueIndex := if layout.endian == .little then index else count - index - 1
    let byte := (bits.toNat / 2 ^ (8 * valueIndex)) % 256
    result := result.push (UInt8.ofNat byte)
  return result

private def readTargetUInt (layout : TargetDataLayout) (bytes : Array UInt8) :
    Except AllocError U128 := do
  if bytes.size > 16 then throw (.scalarBytesTooWide (Size.ofBytes (UInt64.ofNat bytes.size)))
  let mut value := 0
  for index in [:bytes.size] do
    let some byte := bytes[index]? | throw (.invalidSliceEndpoints index (index + 1) bytes.size)
    let valueIndex := if layout.endian == .little then index else bytes.size - index - 1
    value := value + byte.toNat * 2 ^ (8 * valueIndex)
  return BitVec.ofNat 128 value

private def firstNonZero (bytes : Array UInt8) : Option (Nat × UInt8) := Id.run do
  for index in [:bytes.size] do
    match bytes[index]? with
    | some byte => if byte != 0 then return some (index, byte)
    | none => return some (index, 0)
  return none

structure Allocation (Prov : Type := CtfeProvenance) (Extra : Type := Unit) where
  private mk ::
  private rawBytes : Array UInt8
  private size : Size
  private provenance : ProvenanceMap Prov
  private initMask : InitMask
  align : Align
  mutability : Mutability
  extra : Extra
  nativeBuffer : Option NativeBufferOwnership := none

namespace Allocation

def fromBytes (bytes : Array UInt8) (align : Align) (mutability : Mutability) :
    Except AllocError (Allocation Prov Unit) := do
  let align ← checkedAlign align
  let size ← sizeForArray bytes.size
  if _h : bytes.size = size.bytes.toNat then
    return ⟨bytes, size, ProvenanceMap.new, InitMask.new size true,
      align, mutability, (), none⟩
  else
    throw (.storageLengthOverflow bytes.size)

def fromBytesByteAlignedImmutable (bytes : Array UInt8) :
    Except AllocError (Allocation Prov Unit) :=
  fromBytes bytes Align.ONE .Not

/-- `zeroedStorage` is the explicit host `AllocBytes::zeroed` boundary. A
`none` result preserves the source's `MemoryExhausted` failure. The backend's
zeroed-storage contract is checked before an allocation value is returned. -/
def tryNew (size : Size) (align : Align) (init : AllocInit)
    (zeroedStorage : Size → Align → Option (Array UInt8)) :
    Except AllocError (Allocation Prov Unit) := do
  let align ← checkedAlign align
  let bytes ← match zeroedStorage size align with
    | some bytes => pure bytes
    | none => throw .hostMemoryExhausted
  if bytes.size != size.bytes.toNat then
    throw (.storageLengthMismatch size bytes.size)
  if let some (index, value) := firstNonZero bytes then
    throw (.storageBackendNotZeroed index value)
  let initialized := match init with
    | .Uninit => false
    | .Zero => true
  if _h : bytes.size = size.bytes.toNat then
    return ⟨bytes, size, ProvenanceMap.new, InitMask.new size initialized,
      align, .Mut, (), none⟩
  else
    throw (.storageLengthMismatch size bytes.size)

def withExtra (allocation : Allocation Prov Unit) (extra : Extra) :
    Allocation Prov Extra :=
  ⟨allocation.rawBytes, allocation.size,
    allocation.provenance, allocation.initMask, allocation.align,
    allocation.mutability, extra, allocation.nativeBuffer⟩

/-- Map only allocation metadata. Byte storage, size, provenance, init mask,
alignment, and mutability are copied unchanged, matching the source fieldwise
metadata update boundary used by tree-retagging. -/
def mapExtra (allocation : Allocation Prov Extra) (f : Extra → Extra') :
    Allocation Prov Extra' :=
  ⟨allocation.rawBytes, allocation.size, allocation.provenance,
    allocation.initMask, allocation.align, allocation.mutability,
    f allocation.extra, allocation.nativeBuffer⟩

/-- Replace only allocation metadata while retaining all allocation storage
and semantic state. -/
def setExtra (allocation : Allocation Prov Extra) (extra : Extra) :
    Allocation Prov Extra :=
  allocation.mapExtra (fun _ => extra)

/-- Attach once at actual backing creation; metadata transformations preserve
this owner. Cloning bytes must allocate a fresh backing before attaching it. -/
def attachNativeBuffer (allocation : Allocation Prov Extra) (owner : NativeBufferOwnership) :
    Except String (Allocation Prov Extra) := do
  if owner.pointer == 0 then throw "cannot attach null native backing"
  if allocation.nativeBuffer.isSome then throw "allocation already owns native backing"
  pure {allocation with nativeBuffer := some owner}

def withoutNativeBuffer (allocation : Allocation Prov Extra) : Allocation Prov Extra :=
  {allocation with nativeBuffer := none}

def len (allocation : Allocation Prov Extra) : Nat := allocation.rawBytes.size

def byteSize (allocation : Allocation Prov Extra) : Size := allocation.size

def provenanceMap (allocation : Allocation Prov Extra) : ProvenanceMap Prov :=
  allocation.provenance

def initializationMask (allocation : Allocation Prov Extra) : InitMask :=
  allocation.initMask

/-- Source `Allocation::adjust_from_tcx`, used when importing interned global
and thread-local allocations into a machine with a different byte backend or
provenance representation. The two callbacks preserve the source's allocation
and pointer-conversion failure boundaries. The source `ptrs()` assertion is
reported explicitly when byte-fragment provenance is present. -/
def adjustFromTcx [PointerProvenance Prov] {CallbackError HookState : Type}
    (source : Allocation CtfeProvenance Unit) (layout : TargetDataLayout)
    (allocateBytes : Array UInt8 → Align → HookState →
      EStateM.Result CallbackError HookState (Array UInt8))
    (adjustPointer : Pointer CtfeProvenance → HookState →
      EStateM.Result CallbackError HookState (Pointer Prov)) :
    EStateM (AllocationAdjustError CallbackError) HookState (Allocation Prov Unit) :=
  fun initialHookState => Id.run do
    let allocationResult ← match allocateBytes source.rawBytes source.align initialHookState with
      | .ok bytes nextState => pure (bytes, nextState)
      | .error reason nextState => return .error (.byteConversion reason) nextState
    let mut bytes := allocationResult.1
    let mut hookState := allocationResult.2
    if bytes.size != source.rawBytes.size then
      return .error (.allocation (.storageLengthMismatch source.size bytes.size)) hookState
    if source.provenance.byteFragments.isSome then
      return .error (.allocation .allocationHasByteFragmentProvenance) hookState
    let ptrBytes := pointerSize layout
    let mut newProvenance := #[]
    for (offset, sourceProvenance) in source.provenance.ptrs do
      let start := offset.bytes.toNat
      let finish := start + ptrBytes.bytes.toNat
      if finish > bytes.size then
        return .error (.allocation (.invalidSliceEndpoints start finish bytes.size)) hookState
      let pointerBytes := bytes.extract start finish
      let bits ← match readTargetUInt layout pointerBytes with
        | .ok bits => pure bits
        | .error reason => return .error (.allocation reason) hookState
      if bits.toNat > maxU64Nat then
        return .error (.allocation (.pointerBitsDoNotFitOffset bits)) hookState
      let adjusted ← match adjustPointer
          (Pointer.new sourceProvenance (Size.ofBytes (UInt64.ofNat bits.toNat))) hookState with
        | .ok adjusted nextState =>
            hookState := nextState
            pure adjusted
        | .error reason nextState =>
            return .error (.pointerAdjustment reason) nextState
      let encoded ← match targetUIntBytes layout ptrBytes
          (BitVec.ofNat 128 adjusted.offset.bytes.toNat) with
        | .ok encoded => pure encoded
        | .error reason => return .error (.allocation reason) hookState
      bytes := bytes.extract 0 start ++ encoded ++ bytes.extract finish bytes.size
      newProvenance := newProvenance.push (offset, adjusted.provenance)
    let provenance ← match ProvenanceMap.fromPresortedPtrs newProvenance with
      | .ok provenance => pure provenance
      | .error reason =>
          return .error (.allocation (.provenance reason)) hookState
    return .ok ⟨bytes, source.size, provenance, source.initMask, source.align,
      source.mutability, (), none⟩ hookState

private def checkedSlice (allocation : Allocation Prov Extra) (range : AllocRange) :
    Except AllocError (Array UInt8) := do
  if allocation.rawBytes.size != allocation.size.bytes.toNat then
    throw (.storageLengthMismatch allocation.size allocation.rawBytes.size)
  let finish ← range.endExclusive |>.mapError AllocError.memory
  if range.start.bytes > finish.bytes || finish.bytes > allocation.size.bytes then
    throw (.outOfBounds range allocation.size)
  return allocation.rawBytes.extract range.start.bytes.toNat finish.bytes.toNat

/-- Raw bytes with the source method's caller-side bounds precondition made
explicit rather than relying on a host array indexing panic. -/
def getBytesUnchecked (allocation : Allocation Prov Extra) (range : AllocRange) :
    Except AllocError (Array UInt8) :=
  checkedSlice allocation range

/-- Inspect raw bytes outside interpreter execution, including uninitialized
bytes and provenance. The source slice panics for invalid endpoints; Lean
reports that invalid domain explicitly. -/
def inspectWithUninitAndPtrOutsideInterpreter
    (allocation : Allocation Prov Extra) (start finish : Nat) :
    Except AllocError (Array UInt8) := do
  if start > finish || finish > allocation.rawBytes.size then
    throw (.invalidSliceEndpoints start finish allocation.rawBytes.size)
  return allocation.rawBytes.extract start finish

/-- Adopt a snapshot of this allocation's actual native backing storage after
an external host operation. The host must report the very same allocation;
this is not an interpreter write: initialization, provenance, permissions and
extras remain unchanged until source process_native_write/trace processing. -/
def refreshNativeBytes (allocation : Allocation Prov Extra) (bytes : Array UInt8) :
    Except AllocError (Allocation Prov Extra) := do
  unless bytes.size == allocation.size.bytes.toNat do
    throw (.storageLengthMismatch allocation.size bytes.size)
  return {allocation with rawBytes := bytes}

/-- Matches `Allocation::get_bytes_strip_provenance`: check initialization
first, then reject overlapping non-address provenance when required, then
return bytes. `layout` supplies the target pointer width used by the map. -/
def getBytesStripProvenance [PointerProvenance Prov]
    (allocation : Allocation Prov Extra) (layout : TargetDataLayout)
    (range : AllocRange) : Except AllocError (Array UInt8) := do
  match ← (allocation.initMask.isRangeInitialized range).mapError AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  if !PointerProvenance.offsetIsAddr (Prov := Prov) then
    let ptrBytes := pointerSize layout
    let isEmpty ← (allocation.provenance.rangeEmpty range ptrBytes).mapError AllocError.provenance
    if !isEmpty then
      let entries ← (allocation.provenance.getRange range ptrBytes).mapError AllocError.provenance
      let some (provRange, _) := entries[0]?
        | throw .nonEmptyProvenanceWithoutEntry
      let provFinish ← provRange.endExclusive |>.mapError AllocError.memory
      let rangeFinish ← range.endExclusive |>.mapError AllocError.memory
      let badStart := if provRange.start.bytes > range.start.bytes
        then provRange.start else range.start
      let badFinish := if provFinish.bytes < rangeFinish.bytes
        then provFinish else rangeFinish
      let bad ← (AllocRange.fromEndpoints badStart badFinish).mapError AllocError.memory
      throw (.readPointerAsInt (some ⟨range, bad⟩))
  checkedSlice allocation range

/-! Scalar memory access. The source assumes caller-side bounds and alignment;
these Lean methods keep invalid ranges as explicit errors instead of array
panics. -/

def readScalar [DecidableEq Prov] [PointerProvenance Prov]
    (allocation : Allocation Prov Extra) (layout : TargetDataLayout)
    (range : AllocRange) (readProvenance : Bool) :
    Except AllocError (Scalar Prov) := do
  match ← (allocation.initMask.isRangeInitialized range).mapError AllocError.memory with
  | .error bad => throw (.invalidUninitBytes (some ⟨range, bad⟩))
  | .ok () => pure ()
  let bytes ← checkedSlice allocation range
  let bits ← readTargetUInt layout bytes
  if readProvenance then
    let targetSize := pointerSize layout
    if range.size != targetSize then
      throw (.scalarPointerNotTargetSized range.size targetSize)
    let provenance ← match allocation.provenance.readPtr range.start targetSize with
      | .ok provenance => pure provenance
      | .error (.readPartialPointer offset) => throw (.readPartialPointer offset)
      | .error reason => throw (.provenance reason)
    match provenance with
    | some provenance =>
      if bits.toNat > 18446744073709551615 then
        throw (.pointerBitsDoNotFitOffset bits)
      return Scalar.fromPointer layout
        (Pointer.new provenance (Size.ofBytes (UInt64.ofNat bits.toNat)))
    | none =>
      let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      return scalar
  else
    if PointerProvenance.offsetIsAddr (Prov := Prov) then
      let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      return scalar
    let isEmpty ← (allocation.provenance.rangeEmpty range (pointerSize layout)).mapError AllocError.provenance
    if isEmpty then
      let scalar ← (Scalar.fromUInt bits range.size).mapError AllocError.scalar
      return scalar
    throw (.readPointerAsInt none)

/-- The full source `Allocation::write_scalar` state transition. It checks
mutability, decodes the scalar, marks initialization, clears overwritten
provenance against the old bytes, writes target-endian bits, then inserts a
pointer provenance entry when the value is a pointer. -/
def writeScalar (layout : TargetDataLayout) (range : AllocRange)
    (value : Scalar Prov) : EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let bitsAndPointer ← match value.toBitsOrPtrInternal range.size with
    | .ok converted => pure converted
    | .error reason => return .error (.scalar reason) state
  match checkedSlice state range with
  | .error error => return .error error state
  | .ok _ => pure ()
  let nextMask ← match state.initMask.setRange range true with
    | .ok mask => pure mask
    | .error error => return .error (.memory error) state
  let beforeClear := { state with initMask := nextMask }
  match state.provenance.clear range state.rawBytes (pointerSize layout) with
  | .error reason mapAfter =>
    return .error (.provenance reason) { beforeClear with provenance := mapAfter }
  | .ok () clearedMap =>
    let finish := range.start.bytes.toNat + range.size.bytes.toNat
    let start := range.start.bytes.toNat
    let (bits, provenance) := match bitsAndPointer with
      | .bits bits => (bits, none)
      | .pointer pointer => (BitVec.ofNat 128 pointer.offset.bytes.toNat, some pointer.provenance)
    let data ← match targetUIntBytes layout range.size bits with
      | .ok data => pure data
      | .error error => return .error error { beforeClear with provenance := clearedMap }
    let bytes := state.rawBytes.extract 0 start ++ data ++
      state.rawBytes.extract finish state.rawBytes.size
    if bytes.size != state.size.bytes.toNat then
      return .error (.storageLengthMismatch state.size bytes.size)
        { beforeClear with provenance := clearedMap }
    let afterWrite := { beforeClear with rawBytes := bytes, provenance := clearedMap }
    match provenance with
    | none => return .ok () afterWrite
    | some provenance =>
      if range.size != pointerSize layout then
        return .error (.scalarPointerNotTargetSized range.size (pointerSize layout)) afterWrite
      match clearedMap.insertPtr range.start provenance (pointerSize layout) with
      | .error reason mapAfter =>
        return .error (.provenance reason) { afterWrite with provenance := mapAfter }
      | .ok () insertedMap =>
        return .ok () { afterWrite with provenance := insertedMap }

/-- Pointer-valued convenience wrapper around the source scalar write path. -/
def writePointer (layout : TargetDataLayout) (range : AllocRange)
    (pointer : Pointer Prov) : EStateM AllocError (Allocation Prov Extra) Unit :=
  writeScalar layout range (Scalar.fromPointer layout pointer)

private def runProvenanceMutation {α : Type}
    (mutation : EStateM.Result ProvenanceMapError (ProvenanceMap Prov) α)
    (state : Allocation Prov Extra) :
    EStateM.Result AllocError (Allocation Prov Extra) α :=
  match mutation with
  | .ok value provenance => .ok value { state with provenance }
  | .error reason provenance => .error (.provenance reason) { state with provenance }

private def setInitialization (state : Allocation Prov Extra) (range : AllocRange)
    (initialized : Bool) : Except AllocError (Allocation Prov Extra) := do
  let initMask ← state.initMask.setRange range initialized |>.mapError AllocError.memory
  return { state with initMask }

private def overwriteRawBytes (state : Allocation Prov Extra) (range : AllocRange)
    (bytes : Array UInt8) : Except AllocError (Allocation Prov Extra) := do
  let finish ← range.endExclusive |>.mapError AllocError.memory
  let start := range.start.bytes.toNat
  let endIndex := finish.bytes.toNat
  let updated := state.rawBytes.extract 0 start ++ bytes ++
    state.rawBytes.extract endIndex state.rawBytes.size
  if updated.size != state.size.bytes.toNat then
    throw (.storageLengthMismatch state.size updated.size)
  return { state with rawBytes := updated }

/-- Source `get_bytes_unchecked_for_overwrite`: mark bytes initialized and
clear any overlapping provenance before the caller writes new bytes. -/
private def prepareForOverwrite (range : AllocRange) (pointerSize : Size)
    (state : Allocation Prov Extra) :
    EStateM.Result AllocError (Allocation Prov Extra) Unit := Id.run do
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  if range.size.bytes == 0 then return .ok () state
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let initialized ← if range.size.bytes == 0 then pure state else
    match setInitialization state range true with
    | .ok initialized => pure initialized
    | .error reason => return .error reason state
  return runProvenanceMutation
    (initialized.provenance.clear range initialized.rawBytes pointerSize) initialized

/-- Write a finite byte stream into this allocation. The array length is the
exact iterator length used by `write_bytes_ptr`; the range is derived from
that length, and bounds remain an explicit caller-side check. -/
def writeBytes (start : Size) (bytes : Array UInt8) (pointerSize : Size) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  let writeSize ← match sizeForArray bytes.size with
    | .ok size => pure size
    | .error reason => return .error reason state
  let range := allocRange start writeSize
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  if writeSize.bytes == 0 then return .ok () state
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let initialized ← match setInitialization state range true with
    | .ok initialized => pure initialized
    | .error reason => return .error reason state
  let clearedResult := initialized.provenance.clear range initialized.rawBytes pointerSize
  let cleared ← match clearedResult with
    | .ok () provenance => pure { initialized with provenance }
    | .error reason provenance =>
        return .error (.provenance reason) { initialized with provenance }
  match overwriteRawBytes cleared range bytes with
  | .ok updated => return .ok () updated
  | .error reason => return .error reason cleared

/-- Write a repeated byte without materializing an input array. This is the
finite-array counterpart of rustc `write_bytes_ptr` with
`std::iter::repeat_n`: perform the same checked range, mutability,
initialization, and provenance transitions as `writeBytes`, then fill the
already allocated storage in place. -/
def writeRepeatedByte (start : Size) (byte : UInt8) (count : UInt64)
    (pointerSize : Size) : EStateM AllocError (Allocation Prov Extra) Unit :=
  fun state => Id.run do
    let range := allocRange start (Size.ofBytes count)
    match checkedSlice state range with
    | .error reason => return .error reason state
    | .ok _ => pure ()
    if count == 0 then return .ok () state
    if state.mutability != .Mut then return .error .readOnlyAllocation state
    let initialized ← match setInitialization state range true with
      | .ok initialized => pure initialized
      | .error reason => return .error reason state
    let clearedResult := initialized.provenance.clear range initialized.rawBytes pointerSize
    let cleared ← match clearedResult with
      | .ok () provenance => pure { initialized with provenance }
      | .error reason provenance =>
          return .error (.provenance reason) { initialized with provenance }
    let startIndex := start.bytes.toNat
    let mut bytes := cleared.rawBytes
    for offset in [:count.toNat] do
      let index := startIndex + offset
      if h : index < bytes.size then
        bytes := bytes.set index byte h
      else
        return .error (.invalidSliceEndpoints startIndex (index + 1) bytes.size) cleared
    return .ok () { cleared with rawBytes := bytes }

/-- Source `Allocation::write_uninit`: clear initialization first, then clear
overlapping provenance, while leaving the arbitrary byte representation alone. -/
def writeUninit (range : AllocRange) (pointerSize : Size) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  if range.size.bytes == 0 then return .ok () state
  if state.mutability != .Mut then return .error .readOnlyAllocation state
  let uninitialized ← match setInitialization state range false with
    | .ok uninitialized => pure uninitialized
    | .error reason => return .error reason state
  let cleared := uninitialized.provenance.clear range uninitialized.rawBytes pointerSize
  match cleared with
  | .ok () provenance => return .ok () { uninitialized with provenance }
  | .error reason provenance =>
      return .error (.provenance reason) { uninitialized with provenance }

/-- Source `Allocation::clear_provenance`: preserve bytes and initialization,
but remove or fragment all pointer provenance intersecting the checked range. -/
def clearProvenance (range : AllocRange) (pointerSize : Size) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  match checkedSlice state range with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  let cleared := state.provenance.clear range state.rawBytes pointerSize
  match cleared with
  | .ok () provenance => return .ok () { state with provenance }
  | .error reason provenance => return .error (.provenance reason) { state with provenance }

/-- Source `Allocation::process_native_write`: mark the selected range
initialized, then replace provenance in it with wildcard byte fragments. This
is intentionally available only to provenance types with a wildcard. Range
and mutability failures are explicit; a missing wildcard remains an error
after the source-ordered initialization transition. -/
def processNativeWrite [PointerProvenance Prov]
    (layout : TargetDataLayout) (range? : Option AllocRange) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  let range := range?.getD (allocRange Size.ZERO state.size)
  if range.size.bytes != 0 then
    match checkedSlice state range with
    | .error _ => return .error (.nativeWriteRangeOutOfBounds range state.size) state
    | .ok _ => pure ()
  if range.size.bytes != 0 && state.mutability != .Mut then
    return .error .readOnlyAllocation state
  let initialized ← if range.size.bytes == 0 then pure state else
    match setInitialization state range true with
    | .ok initialized => pure initialized
    | .error reason => return .error reason state
  return runProvenanceMutation
    (initialized.provenance.writeWildcards range initialized.rawBytes (pointerSize layout))
    initialized

/-- Source `Allocation::provenance_merge_bytes`: attempt to coalesce complete
byte-fragment pointers. A `false` result may retain successful earlier
coalescings, exactly as the source map iteration does. -/
def provenanceMergeBytes [DecidableEq Prov]
    (layout : TargetDataLayout) :
    EStateM AllocError (Allocation Prov Extra) Bool := fun state => Id.run do
  match state.provenance.mergeBytes (pointerSize layout) with
  | .ok merged provenance => return .ok merged { state with provenance }
  | .error reason provenance => return .error (.provenance reason) { state with provenance }

/-- Source allocation-level half of `mem_copy_repeatedly`. Pointer resolution,
access checks, and machine hooks are supplied by the caller. The source's
initialization and provenance snapshots are prepared before destination
overwrite clears its old metadata. -/
def copyRepeatedly
    (source : Allocation Prov Extra) (sourceRange : AllocRange) (destStart : Size)
    (repeatCount : UInt64) (pointerSize : Size) (sameAllocation nonoverlapping : Bool) :
    EStateM AllocError (Allocation Prov Extra) Unit := fun state => Id.run do
  let sourceBytes ← match checkedSlice source sourceRange with
    | .error reason => return .error reason state
    | .ok sourceBytes => pure sourceBytes
  let totalSize ← match Size.mul sourceRange.size repeatCount with
    | .ok size => pure size
    | .error reason => return .error (.memory (.sizeError reason)) state
  let destRange := allocRange destStart totalSize
  match checkedSlice state destRange with
  | .error reason => return .error reason state
  | .ok _ => pure ()
  let provenance ← match source.provenance.prepareCopy sourceRange source.rawBytes pointerSize with
    | .ok copy => pure copy
    | .error reason => return .error (.provenance reason) state
  let initialized ← match source.initMask.prepareCopy sourceRange with
    | .ok copy => pure copy
    | .error reason => return .error (.memory reason) state
  let prepared := prepareForOverwrite destRange pointerSize state
  let afterClear ← match prepared with
    | .ok () updated => pure updated
    | .error reason updated => return .error reason updated
  if initialized.noBytesInit then
    let uninitResult := Allocation.writeUninit destRange pointerSize afterClear
    match uninitResult with
    | .error reason updated => return .error reason updated
    | .ok () updated => return .ok () updated
  if sameAllocation && nonoverlapping then
    let sourceFinish ← match sourceRange.endExclusive with
      | .ok finish => pure finish
      | .error reason => return .error (.memory reason) afterClear
    let firstDestFinish ← match (allocRange destStart sourceRange.size).endExclusive with
      | .ok finish => pure finish
      | .error reason => return .error (.memory reason) afterClear
    if sourceRange.start.bytes < firstDestFinish.bytes && destStart.bytes < sourceFinish.bytes then
      return .error .copyRangesOverlap afterClear
  if repeatCount > 1 && !nonoverlapping then
    return .error .repeatedCopyRequiresNonoverlapping afterClear
  if sourceRange.size.bytes == 1 && repeatCount == 0 && !initialized.noBytesInit then
    return .error .singleByteZeroCountCopy afterClear
  let mut copiedBytes := #[]
  for _ in [:repeatCount.toNat] do
    copiedBytes := copiedBytes ++ sourceBytes
  let afterBytes ← match overwriteRawBytes afterClear destRange copiedBytes with
    | .ok updated => pure updated
    | .error reason => return .error reason afterClear
  let afterInit ← match afterBytes.initMask.applyCopy initialized
      (allocRange destStart sourceRange.size) repeatCount with
    | .ok initMask => pure { afterBytes with initMask }
    | .error reason => return .error (.memory reason) afterBytes
  match afterInit.provenance.applyCopy provenance
      (allocRange destStart sourceRange.size) repeatCount with
  | .ok () provenance => return .ok () { afterInit with provenance }
  | .error reason provenance =>
      return .error (.provenance reason) { afterInit with provenance }

/-- The source `mem_copy` operation is a one-copy specialization. -/
def copy
    (source : Allocation Prov Extra) (sourceRange : AllocRange) (destStart : Size)
    (pointerSize : Size) (sameAllocation nonoverlapping : Bool) :
    EStateM AllocError (Allocation Prov Extra) Unit :=
  copyRepeatedly source sourceRange destStart 1 pointerSize sameAllocation nonoverlapping

/-- Source allocation mutability is a public field. This update preserves
all byte, initialization, provenance and allocation-extra state. -/
def withMutability (self : Allocation Prov Extra) (mutability : Mutability) :
    Allocation Prov Extra :=
  ⟨self.rawBytes, self.size, self.provenance, self.initMask, self.align, mutability, self.extra, self.nativeBuffer⟩

/-- Validated serialization boundary for an interned compiler allocation.
Unlike writes, importing its image does not initialize bytes, clear provenance,
or change the byte representation of pointers. -/
def fromCompilerImage (bytes : Array UInt8) (align : Align) (mutability : Mutability)
    (mask : InitMask) (provenance : ProvenanceMap CtfeProvenance) (pointerSize : Size) :
    Except AllocError (Allocation CtfeProvenance Unit) := do
  let align ← checkedAlign align
  let size ← sizeForArray bytes.size
  if mask.len != size then throw (.storageLengthMismatch size mask.len.bytes.toNat)
  for i in [:bytes.size] do
    let _ ← (mask.get (Size.ofBytes (UInt64.ofNat i))).mapError AllocError.memory
  if pointerSize.bytes == 0 then throw (.provenance .pointerSizeZero)
  if provenance.byteFragments.isSome then throw .allocationHasByteFragmentProvenance
  let _ ← (ProvenanceMap.fromPresortedPtrs provenance.ptrs).mapError AllocError.provenance
  let mut previousEnd := 0
  for (offset, _) in provenance.ptrs do
    let start := offset.bytes.toNat
    let finish := start + pointerSize.bytes.toNat
    if start < previousEnd then throw (.provenance .insertOverlapsExistingProvenance)
    if finish > bytes.size then throw (.outOfBounds (allocRange offset pointerSize) size)
    previousEnd := finish
  return ⟨bytes, size, provenance, mask, align, mutability, (), none⟩

end Allocation

end Miri.Memory
