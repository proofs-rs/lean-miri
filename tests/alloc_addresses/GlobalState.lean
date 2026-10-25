import Miri.Memory.AllocAddresses.GlobalState

open Miri.ABI Miri.Concurrency Miri.Memory Miri.Memory.AllocAddresses

private def id1 : AllocId := ⟨1, by decide⟩
private def id2 : AllocId := ⟨2, by decide⟩
private def id3 : AllocId := ⟨3, by decide⟩
private def id4 : AllocId := ⟨4, by decide⟩
private def tag : BorTag := BorTag.one

private def sz (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def algn (exponent : Nat) : Align := ⟨exponent⟩

private def choices (reuse cross : Bool) (index : Nat) (slack : Fin 16) :
    AddressRandomChoices := ⟨reuse, cross, index, slack⟩

private def errored : Except ε α → Bool
  | .error _ => true
  | .ok _ => false

private def donorClock : VClock :=
  VClock.ofList [VTimestamp.ofPacked 24 (by decide)]

private def info (thread : UInt32 := 0) : AllocationAddressInfo :=
  ⟨.liveData, true, sz 8, algn 2, some .other, thread⟩

private def idText (id : AllocId) : String := toString id.value

private def baseText (state : GlobalAddressState) : String :=
  String.intercalate "," (state.baseAddr.toList.map fun entry =>
    s!"{idText entry.allocId}:{entry.address}")

private def inverseText (state : GlobalAddressState) : String :=
  String.intercalate "," (state.intToPtrMap.toList.map fun entry =>
    s!"{entry.address}:{idText entry.allocId}")

private def exposedText (state : GlobalAddressState) : String :=
  String.intercalate "," (state.exposed.toList.map idText)

private def stateText (state : GlobalAddressState) : String :=
  s!"base[{baseText state}] inverse[{inverseText state}] exposed[{exposedText state}]"

private def requireState (result : Except AddressStateError GlobalAddressState) : IO GlobalAddressState := do
  match result with
  | .ok state => pure state
  | .error error => throw (IO.userError (toString error))

private def emitAssignment (tag : String) (result : AddressStateResult AddressAssignment) : IO Unit := do
  let output := match result.outcome with
    | .error error => s!"E {toString error}"
    | .ok (.ready address) => s!"O {address}"
    | .ok (.acquireRequired id address clock) =>
        s!"A {idText id} {address} {clockKey clock}"
  IO.println s!"B {tag} {output} {stateText result.state}"
where
  clockKey (clock : VClock) : Nat :=
    match clock.asList.head? with | none => 0 | some timestamp => timestamp.time

def main : IO Unit := do
  let config : AddressReuseConfig := ⟨0.5, 0.5⟩
  let mut state ← requireState (GlobalAddressState.new .default .managed 1000 2000 config)
  let first := state.addrFromAllocId id1 (some info) (choices false false 0 ⟨0, by decide⟩)
  state := first.state
  emitAssignment "fresh" first
  let cached := state.addrFromAllocId id1 none (choices true true 0 ⟨15, by decide⟩)
  state := cached.state
  emitAssignment "cached-without-info" cached

  let exposed := state.exposeProvenance (.concrete id1 tag) (some true) false none
  state := exposed.state
  IO.println s!"X expose-id1 {!errored exposed.outcome} {stateText state}"

  let hooks : AddressLookupHooks := {
    sizeOf := fun id => if id == id1 || id == id2 then some (sz 8) else none
    isLive := fun id => if id == id1 || id == id2 then some true else some false }
  let lookupBase := state.allocIdFromAddr 1000 (Int64.ofInt 0) hooks
  let lookupInterior := state.allocIdFromAddr 1003 (Int64.ofInt 0) hooks
  let lookupEnd := state.allocIdFromAddr 1008 (Int64.ofInt 0) hooks
  let lookupNegativeEnd := state.allocIdFromAddr 1008 (Int64.ofInt (-1)) hooks
  IO.println s!"L exact {lookupBase.map (·.map idText)}"
  IO.println s!"L interior {lookupInterior.map (·.map idText)}"
  IO.println s!"L end {lookupEnd.map (·.map idText)}"
  IO.println s!"L negative-end {lookupNegativeEnd.map (·.map idText)}"

  let missingKindInfo := { info with memoryKind := none }
  emitAssignment "missing-memory-kind"
      (state.addrFromAllocId id4 (some missingKindInfo) (choices false false 0 ⟨0, by decide⟩))

  let freed := state.freeAllocId id1 (sz 8) (algn 2) .other 0 true (fun _ => donorClock)
  state := freed.state
  IO.println s!"F free-id1 {!errored freed.outcome} {stateText state}"

  let assigned2 := state.addrFromAllocId id2 (some (info 1))
      (choices true true 0 ⟨0, by decide⟩)
  state := assigned2.state
  emitAssignment "cross-thread-pending" assigned2
  let failedAcquire := GlobalAddressState.completeAcquire assigned2 (.error "clock hook failed")
  emitAssignment "cross-thread-hook-failure" failedAcquire
  let completed := GlobalAddressState.completeAcquire assigned2 (.ok ())
  state := completed.state
  emitAssignment "cross-thread-acquired" completed

  let exposed2 := state.exposeProvenance (.concrete id2 tag) (some true) false none
  state := exposed2.state

  let ptrResult := state.ptrFromAddrCast 1003 true
  match ptrResult.outcome with
  | .error error => IO.println s!"P int-to-pointer error {toString error}"
  | .ok (pointer, warning) =>
      let .some .wildcard := pointer.provenance
        | throw (IO.userError "integer cast did not preserve wildcard provenance")
      let got := state.ptrGetAlloc (Pointer.new .wildcard (sz 1003)) (Int64.ofInt 1)
          hooks ⟨sz 8⟩
      let gotText := match got with
        | .error error => s!"E {toString error}"
        | .ok none => "none"
        | .ok (some (id, relative)) => s!"{idText id}:{relative.bytes}"
      IO.println s!"P wildcard {warning} {gotText}"

  let exposedWithTracker := state.exposeProvenance (.concrete id2 tag) (some true) true none
  state := exposedWithTracker.state
  IO.println s!"X tracker-hook {errored exposedWithTracker.outcome} {stateText state}"

  let typeInfo : AllocationAddressInfo :=
    ⟨.typeId, true, Size.ZERO, Align.ONE, some .other, 0⟩
  emitAssignment "type-id-requires-memory-kind"
      (state.addrFromAllocId id3 (some { typeInfo with memoryKind := none })
        (choices false false 0 ⟨0, by decide⟩))
  let typeId := state.addrFromAllocId id3 (some typeInfo) (choices false false 0 ⟨0, by decide⟩)
  state := typeId.state
  emitAssignment "type-id-zero" typeId
  let wrappingPointer := Pointer.new (.concrete id3 tag) (sz 4294967299)
  let wrapped := state.ptrGetAlloc wrappingPointer (Int64.ofInt 1) hooks ⟨sz 4⟩
  let wrappedText := match wrapped with
    | .error error => s!"E {toString error}"
    | .ok none => "none"
    | .ok (some (id, relative)) => s!"{idText id}:{relative.bytes}"
  IO.println s!"P target32-wrap {wrappedText}"
  state := state.removeUnreachableAllocs #[id2, id3]
  IO.println s!"G retain-live-only {stateText state}"

  let strict ← requireState (GlobalAddressState.new .strict .managed 10 20 config)
  IO.println s!"P strict-cast {errored (strict.ptrFromAddrCast 5 true).outcome}"
  IO.println s!"L strict-lookup {errored (strict.allocIdFromAddr 5 (Int64.ofInt 0) hooks)}"

  let tiny ← requireState (GlobalAddressState.new .default .managed 10 10 config)
  let exhausted := tiny.addrFromAllocId id4 (some (info)) (choices false false 0 ⟨0, by decide⟩)
  let nextAfterFailure := exhausted.state.generation.map
      fun generation => generation.generator.nextBaseAddr
  emitAssignment "generator-exhaustion" exhausted
  IO.println s!"B exhaustion-retained-next {nextAfterFailure}"

  let native ← requireState (GlobalAddressState.new .default .nativeLib 0 100 config)
  let nativeMissing := native.addrFromAllocId id4 (some (info))
      (choices false false 0 ⟨0, by decide⟩)
  emitAssignment "native-hook-required" nativeMissing
  let nativeReady := native.addrFromAllocId id4 (some (info))
      (choices false false 0 ⟨0, by decide⟩) { externalAddress := some 5000 }
  emitAssignment "native-hook-address" nativeReady

theorem strict_mode_rejects_integer_cast (state : GlobalAddressState) (address : UInt64)
    (h : state.provenanceMode = .strict) :
    (state.ptrFromAddrCast address false).outcome = .error .strictIntegerToPointerCast := by
  simp [GlobalAddressState.ptrFromAddrCast, h]
