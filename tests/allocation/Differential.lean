import Miri.Memory.Allocation

open Miri.ABI
open Miri.Memory

private def size (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def range (start finish : Nat) : AllocRange :=
  allocRange (size start) (size (finish - start))

private def requireOk {α : Type} (label : String) (result : Except AllocError α) : IO α := do
  match result with
  | .ok value => pure value
  | .error reason => throw (IO.userError s!"{label}: {reason}")

private def bytesText (bytes : Array UInt8) : String :=
  String.intercalate "," (bytes.toList.map fun byte => toString byte.toNat)

private def endpoint (range : AllocRange) : Nat :=
  match range.endExclusive with
  | .ok finish => finish.bytes.toNat
  | .error _ => range.start.bytes.toNat

private def showRead (result : Except AllocError (Array UInt8)) : String :=
  match result with
  | .ok bytes => s!"O{bytesText bytes}"
  | .error (.invalidUninitBytes (some bad)) =>
      s!"U{bad.bad.start.bytes.toNat}:{endpoint bad.bad}"
  | .error (.invalidUninitBytes none) => "U-"
  | .error (.readPointerAsInt (some bad)) =>
      s!"P{bad.bad.start.bytes.toNat}:{endpoint bad.bad}"
  | .error (.readPointerAsInt none) => "P-"
  | .error (.readPartialPointer offset) => s!"R{offset.bytes.toNat}"
  | .error error => s!"E{error}"

private def showAdjustedScalar (value : Scalar CtfeProvenance) : String :=
  match value.toBitsOrPtrInternal (size 8) with
  | .ok (.pointer pointer) =>
      s!"P:8:{pointer.offset.bytes.toNat}:{pointer.provenance.allocId.value.toNat}"
  | .ok (.bits bits) => s!"I:8:{bits.toNat}"
  | .error error => s!"E:{error}"

private def showTestProvenance : Provenance → String
  | .wildcard => "Wild"
  | .concrete id _ => s!"Concrete({id.value.toNat})"

private def inspectWildcardFragments (tag : String)
    (allocation : Allocation Provenance Unit) (len : Nat) : IO Unit := do
  let fragments := allocation.provenanceMap.byteFragments.getD #[]
  let values := (List.range len).map fun position =>
    match fragments.find? (fun entry => entry.1.bytes.toNat == position) with
    | some (_, fragment) => s!"{fragment.idx.toNat}:{showTestProvenance fragment.prov}"
    | none => "-"
  IO.println s!"N {tag} {String.intercalate "," values}"
  let total := allocation.provenanceMap.ptrs.size + fragments.size
  IO.println s!"N {tag}_merge {total}"

private def inspect (tag : String) (allocation : Allocation CtfeProvenance Unit)
    (layout : TargetDataLayout) : IO Unit := do
  let len := allocation.len
  let alignBytes ← match Align.bytes allocation.align with
    | .ok bytes => pure bytes.toNat
    | .error reason => throw (IO.userError s!"invalid allocation alignment: {reason}")
  IO.println s!"A {tag} {len} {alignBytes}"
  let rawBytes ← requireOk s!"raw bytes {tag}"
    (allocation.getBytesUnchecked (range 0 len))
  IO.println s!"W {tag} {bytesText rawBytes}"
  let mut ranges := #[(0, 0), (0, len), (len, len)]
  if len > 0 then
    ranges := ranges ++ #[(0, 1), (len - 1, len), (0, len + 1), (len, len + 1)]
  if len >= 2 then ranges := ranges ++ #[(1, 2), (1, len)]
  for (start, finish) in ranges do
    let result := allocation.getBytesStripProvenance layout (range start finish)
    IO.println s!"R {tag} {start} {finish} {showRead result}"

private def tryNew (sizeBytes : Nat) (init : AllocInit) :
    IO (Allocation CtfeProvenance Unit) := do
  let allocation ← requireOk "tryNew"
    (Allocation.tryNew (size sizeBytes) Align.ONE init
      (fun requested _ => some (Array.replicate requested.bytes.toNat 0)))
  pure allocation

def main : IO Unit := do
  let layout : TargetDataLayout := ⟨.big, .w64⟩
  let raw ← requireOk "fromBytes"
    (Allocation.fromBytes #[3, 1, 4, 1, 5] Align.ONE .Not)
  inspect "raw" raw layout

  for (tag, init) in #[("uninit0", AllocInit.Uninit), ("zero0", AllocInit.Zero)] do
    inspect tag (← tryNew 0 init) layout
  for (tag, init) in #[("uninit5", AllocInit.Uninit), ("zero5", AllocInit.Zero)] do
    inspect tag (← tryNew 5 init) layout
  for len in [63, 64, 65] do
    let allocation ← tryNew len .Uninit
    IO.println s!"B {len} {showRead (allocation.getBytesStripProvenance layout (range (len - 1) len))}"

  let uninitPointerSlot ← tryNew 8 .Uninit
  let id ← match AllocId.ofUInt64 1 with
    | some id => pure id
    | none => throw (IO.userError "test allocation ID 1 was rejected")
  let provenance ← match CtfeProvenance.fromAllocId id with
    | .ok provenance => pure provenance
    | .error .allocationIdUsesFlagBits =>
        throw (IO.userError "test CTFE allocation ID uses the packed flag bits")
  let pointer := Pointer.new provenance (size 0x1234)
  let pointerScalar : Scalar CtfeProvenance := Scalar.fromPointer layout pointer
  match Allocation.writePointer layout (range 0 8) pointer uninitPointerSlot with
  | .ok () allocation => inspect "pointer_scalar" allocation layout
  | .error reason _ => throw (IO.userError s!"pointer scalar write failed: {reason}")

  let byteOps ← tryNew 8 .Uninit
  let byteOps ← match Allocation.writeScalar layout (range 0 8) pointerScalar byteOps with
    | .ok () allocation => pure allocation
    | .error reason _ => throw (IO.userError s!"setup scalar write failed: {reason}")
  let byteOps ← match Allocation.writeBytes (size 3) #[0xaa] (size 8) byteOps with
    | .ok () allocation => pure allocation
    | .error reason _ => throw (IO.userError s!"byte-stream write failed: {reason}")
  IO.println s!"X write_bytes {showRead (byteOps.getBytesStripProvenance layout (range 0 8))}"
  let byteOps ← match Allocation.clearProvenance (range 0 8) (size 8) byteOps with
    | .ok () allocation => pure allocation
    | .error reason _ => throw (IO.userError s!"clear provenance failed: {reason}")
  IO.println s!"X clear_provenance {showRead (byteOps.getBytesStripProvenance layout (range 0 8))}"
  let byteOps ← match Allocation.writeUninit (range 2 4) (size 8) byteOps with
    | .ok () allocation => pure allocation
    | .error reason _ => throw (IO.userError s!"write uninit failed: {reason}")
  IO.println s!"X write_uninit {showRead (byteOps.getBytesStripProvenance layout (range 1 5))}"

  let sourceId ← match AllocId.ofUInt64 1 with
    | some id => pure id
    | none => throw (IO.userError "source allocation ID 1 was rejected")
  let targetId ← match AllocId.ofUInt64 2 with
    | some id => pure id
    | none => throw (IO.userError "target allocation ID 2 was rejected")
  let sourceProv ← match CtfeProvenance.fromAllocId sourceId with
    | .ok prov => pure prov
    | .error _ => throw (IO.userError "source provenance construction failed")
  let targetProv ← match CtfeProvenance.fromAllocId targetId with
    | .ok prov => pure prov
    | .error _ => throw (IO.userError "target provenance construction failed")
  let source ← requireOk "adjust source allocation"
    (Allocation.tryNew (Prov := CtfeProvenance) (size 8) Align.EIGHT .Uninit
      (fun requested _ => some (Array.replicate requested.bytes.toNat 0)))
  let source ← match Allocation.writePointer layout (range 0 8)
      (Pointer.new sourceProv (size 0x1234)) source with
    | .ok () allocation => pure allocation
    | .error reason _ => throw (IO.userError s!"adjust source pointer setup failed: {reason}")
  let allocateBytes : Array UInt8 → Align → Array String →
      EStateM.Result String (Array String) (Array UInt8) :=
    fun bytes align state =>
      .ok bytes (state.push s!"B{bytes.size}:{(Align.bytes align).toOption.getD 0}")
  let adjustPointer : Pointer CtfeProvenance → Array String →
      EStateM.Result String (Array String) (Pointer CtfeProvenance) :=
    fun pointer state =>
      .ok (Pointer.new targetProv (size (pointer.offset.bytes.toNat + 0x20)))
        (state.push s!"P{pointer.provenance.allocId.value.toNat}:{pointer.offset.bytes.toNat}")
  match Allocation.adjustFromTcx source layout allocateBytes adjustPointer #[] with
  | .error reason _ => throw (IO.userError s!"adjust_from_tcx failed: {repr reason}")
  | .ok adjusted callbackOrder =>
    IO.println s!"T adjust_callbacks {String.intercalate "," callbackOrder.toList}"
    IO.println s!"T adjust_bytes {bytesText (← requireOk "adjusted bytes" (adjusted.getBytesUnchecked (range 0 8)))}"
    let read ← match adjusted.readScalar layout (range 0 8) true with
      | .ok scalar => pure scalar
      | .error reason => throw (IO.userError s!"adjusted scalar read failed: {reason}")
    IO.println s!"T adjust_read {showAdjustedScalar read}"
    let alignment ← match Align.bytes adjusted.align with
      | .ok bytes => pure bytes.toNat
      | .error reason => throw (IO.userError s!"adjusted alignment failed: {reason}")
    let initialized := match adjusted.initializationMask.isRangeInitialized (range 0 8) with
      | .ok (.ok ()) => true
      | _ => false
    let mutability := match adjusted.mutability with
      | .Mut => "Mut"
      | .Not => "Not"
    IO.println s!"T adjust_meta {adjusted.len}:{alignment}:{mutability}:{initialized}"

  let emptySource ← requireOk "empty adjustment source"
    (Allocation.fromBytes (Prov := CtfeProvenance) #[9, 8, 7] Align.ONE .Not)
  let emptyAllocateBytes : Array UInt8 → Align → Array String →
      EStateM.Result String (Array String) (Array UInt8) :=
    fun bytes align calls =>
      .ok bytes (calls.push s!"B{bytes.size}:{(Align.bytes align).toOption.getD 0}")
  let noPointerAdjustment : Pointer CtfeProvenance → Array String →
      EStateM.Result String (Array String) (Pointer CtfeProvenance) :=
    fun _ calls => .error "unexpected pointer adjustment" calls
  match Allocation.adjustFromTcx emptySource layout emptyAllocateBytes noPointerAdjustment #[] with
  | .error reason _ => throw (IO.userError s!"pointer-free adjustment failed: {repr reason}")
  | .ok adjusted calls =>
    IO.println s!"T adjust_no_ptrs {String.intercalate "," calls.toList}:{bytesText (← requireOk "pointer-free adjusted bytes"
      (adjusted.getBytesUnchecked (range 0 3)))}"

  let fragmentSource ← requireOk "fragment adjustment source"
    (Allocation.tryNew (Prov := CtfeProvenance) (size 8) Align.ONE .Uninit
      (fun requested _ => some (Array.replicate requested.bytes.toNat 0)))
  let fragmentSource ← match Allocation.writePointer layout (range 0 8)
      (Pointer.new sourceProv (size 0x1234)) fragmentSource with
    | .ok () allocation => pure allocation
    | .error reason _ => throw (IO.userError s!"fragment source pointer setup failed: {reason}")
  let fragmentSource ← match Allocation.writeBytes (size 3) #[0xaa] (size 8) fragmentSource with
    | .ok () allocation => pure allocation
    | .error reason _ => throw (IO.userError s!"fragment source byte setup failed: {reason}")
  let fragmentAllocateBytes : Array UInt8 → Align → Array String →
      EStateM.Result String (Array String) (Array UInt8) :=
    fun bytes align callbacks =>
      .ok bytes (callbacks.push s!"B{bytes.size}:{(Align.bytes align).toOption.getD 0}")
  let fragmentPointerAdjustment : Pointer CtfeProvenance → Array String →
      EStateM.Result String (Array String) (Pointer CtfeProvenance) :=
    fun _ callbacks => .error "pointer callback should not run" callbacks
  match Allocation.adjustFromTcx fragmentSource layout
      fragmentAllocateBytes fragmentPointerAdjustment #[] with
  | .error (.allocation .allocationHasByteFragmentProvenance) callbacks =>
      IO.println s!"T adjust_fragments true:{String.intercalate "," callbacks.toList}"
  | .error reason _ => throw (IO.userError s!"wrong fragment-adjustment failure: {repr reason}")
  | .ok _ _ => throw (IO.userError "fragment provenance passed the interned-allocation assertion")

  let nativeSource ← requireOk "native-write allocation"
    (Allocation.tryNew (Prov := Provenance) (size 8) Align.EIGHT .Uninit
      (fun requested _ => some (Array.replicate requested.bytes.toNat 0)))
  let nativeId ← match AllocId.ofUInt64 7 with
    | some id => pure id
    | none => throw (IO.userError "native test allocation ID was rejected")
  let nativeProv := Provenance.concrete nativeId .one
  let nativePointer := Pointer.new nativeProv (size 0x0102030405060708)
  let nativeSource ← match Allocation.writePointer layout (range 0 8) nativePointer nativeSource with
    | .ok () allocation => pure allocation
    | .error reason _ => throw (IO.userError s!"native pointer setup failed: {reason}")
  let before := bytesText (← requireOk "native source bytes" (nativeSource.getBytesUnchecked (range 0 8)))
  let native ← match Allocation.processNativeWrite layout (some (range 3 5)) nativeSource with
    | .ok () allocation => pure allocation
    | .error reason _ => throw (IO.userError s!"native write failed: {reason}")
  let initialized := match native.initializationMask.isRangeInitialized (range 0 8) with
    | .ok (.ok ()) => true
    | _ => false
  let after := bytesText (← requireOk "native result bytes" (native.getBytesUnchecked (range 0 8)))
  IO.println s!"N native {before}:{initialized}:{after}"
  inspectWildcardFragments "native" native 8
  let (merged, nativeAfterMerge) ← match Allocation.provenanceMergeBytes layout native with
    | .ok merged allocation => pure (merged, allocation)
    | .error reason _ => throw (IO.userError s!"native provenance merge failed: {reason}")
  IO.println s!"N native_merge_result {merged}"
  inspectWildcardFragments "native_after_merge" nativeAfterMerge 8

  let zeroNative ← requireOk "zero native-write allocation"
    (Allocation.tryNew (Prov := Provenance) (size 0) Align.ONE .Uninit
      (fun requested _ => some (Array.replicate requested.bytes.toNat 0)))
  let zeroNative ← match Allocation.processNativeWrite layout (some (range 9 9)) zeroNative with
    | .ok () allocation => pure allocation
    | .error reason _ => throw (IO.userError s!"zero-sized native write failed: {reason}")
  let zeroInitialized := match zeroNative.initializationMask.isRangeInitialized (range 0 0) with
    | .ok (.ok ()) => true
    | _ => false
  IO.println s!"N native_zero {zeroNative.len}:{zeroInitialized}"
  inspectWildcardFragments "native_zero" zeroNative 0
  let (zeroMerged, _) ← match Allocation.provenanceMergeBytes layout zeroNative with
    | .ok merged allocation => pure (merged, allocation)
    | .error reason _ => throw (IO.userError s!"zero native provenance merge failed: {reason}")
  IO.println s!"N native_zero_merge {zeroMerged}"

  let noWildcard ← requireOk "no-wildcard native-write allocation"
    (Allocation.tryNew (Prov := CtfeProvenance) (size 8) Align.ONE .Uninit
      (fun requested _ => some (Array.replicate requested.bytes.toNat 0)))
  match Allocation.processNativeWrite layout (some (range 0 1)) noWildcard with
  | .error (.provenance .missingWildcard) afterMark =>
    let initialized := match afterMark.initializationMask.isRangeInitialized (range 0 1) with
      | .ok (.ok ()) => true
      | _ => false
    IO.println s!"N native_missing_wildcard true:{initialized}"
  | .error reason _ => throw (IO.userError s!"wrong no-wildcard failure: {reason}")
  | .ok () _ => throw (IO.userError "native write succeeded without wildcard provenance")
