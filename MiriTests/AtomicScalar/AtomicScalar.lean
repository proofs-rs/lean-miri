import Miri.Concurrency.AtomicScalarMemory
import Miri.Memory.CtfeProvenance

open Miri.ABI Miri.Concurrency Miri.Interpreter
open Miri.Memory Miri.MIR

private def layout : TargetDataLayout :=
  { endian := .little, pointerWidth := .w64 }

private def size (bytes : Nat) : Size := Size.ofBytes (UInt64.ofNat bytes)
private def byteRange : AllocRange := { start := size 0, size := size 1 }
private def mainIndex : VectorIdx := VectorIdx.ofU32 0 (by decide)

private def unwrap {Error Value : Type} (message : String)
    (result : Except Error Value) : IO Value :=
  match result with
  | .ok value => pure value
  | .error _ => throw (IO.userError message)

private def makeState (weakMemory : Bool) :
    Except AllocError (AtomicScalarMemory Provenance) := do
  let memory ← Allocation.fromBytes #[1] Align.ONE .Mut
  let initialGlobal := GlobalState.initial false weakMemory
  let global := { initialGlobal with multiThreaded := true }
  let clocks := VClockAlloc.newAllocation
    (ByteSize.ofU64 1 (by decide)) VTimestamp.ZERO mainIndex
  pure {
    memory := memory
    concurrency := {
      global := global
      allocation := clocks
      weakMemoryAllocation := if weakMemory then some StoreBufferAlloc.newAllocation else none
    }
  }

private def readByte (state : AtomicScalarMemory Provenance) : Except AllocError UInt8 := do
  let scalar ← state.memory.readScalar layout byteRange false
  scalar.toUInt8 |>.mapError (fun e => .scalar e)

def main : IO Unit := do
  let manager := ThreadManager.initial false
  let initial ← match makeState true with
    | .error _ => throw (IO.userError "could not create one-byte scalar allocation")
    | .ok state => pure state
  let stored := atomicScalarStore initial manager layout byteRange false
    (Scalar.fromScalarInt (ScalarInt.ofUInt8 42)) .Relaxed
  if stored.requiredHooks != [.atomicAccessCheck, .interpreterBeforeMemoryWrite] then
    throw (IO.userError "atomic store failed to retain its interpreter hook obligations")
  match stored.asOperationalOutcome with
  | .blocked (.interpreterHooks hooks) =>
    if hooks != stored.requiredHooks then
      throw (IO.userError "operational outcome lost the pending source-hook list")
  | _ => throw (IO.userError "partial atomic dispatch was reported as a return")
  match stored.outcome with
  | .error _ => throw (IO.userError "atomic store dispatch failed")
  | .ok () => pure ()
  let load := atomicScalarLoad stored.state manager layout byteRange false .Relaxed 0
  if load.requiredHooks != [.atomicAccessCheck, .interpreterBeforeMemoryRead] then
    throw (IO.userError "atomic load failed to retain its interpreter hook obligations")
  let loaded ← match load.outcome with
    | .error _ => throw (IO.userError "atomic load dispatch failed")
    | .ok value => pure value
  if (← unwrap "loaded scalar was not a u8" loaded.toUInt8) != 42 then
    throw (IO.userError "atomic load did not choose the actual buffered scalar")
  let addTwo := Scalar.fromScalarInt (ScalarInt.ofUInt8 2)
  let rmw := atomicScalarRmw load.state manager layout byteRange false
    (.mir .Add false) { size := size 1, kind := .u8 } addTwo .Relaxed
  let old ← match rmw.outcome with
    | .error _ => throw (IO.userError "atomic RMW dispatch failed")
    | .ok value => pure value
  if old.toUInt8 != .ok 42 then
    throw (IO.userError "atomic RMW returned the wrong old scalar")
  if (← unwrap "RMW allocation read failed" (readByte rmw.state)) != 44 then
    throw (IO.userError "atomic RMW did not update actual allocation bytes")
  if rmw.requiredHooks !=
      [.atomicAccessCheck, .interpreterBeforeMemoryRead, .interpreterBeforeMemoryWrite] then
    throw (IO.userError "atomic RMW failed to retain its interpreter hook obligations")
  let unsupportedRmw := atomicScalarRmw load.state manager layout byteRange false
    (.mir .Div false) { size := size 1, kind := .u8 } addTwo .Relaxed
  match unsupportedRmw.outcome with
  | .error (.integerOperation (.invalidBinaryOperator .Div)) => pure ()
  | _ => throw (IO.userError "unsupported atomic RMW operation was treated as successful")
  if unsupportedRmw.requiredHooks.contains .interpreterBeforeMemoryWrite then
    throw (IO.userError "RMW operator failure requested a write hook before source write")
  IO.println "atomic-scalar:store-load-rmw:1->42->44:hooks-pending"

  let expect44 := Scalar.fromScalarInt (ScalarInt.ofUInt8 44)
  let replacement := Scalar.fromScalarInt (ScalarInt.ofUInt8 50)
  let exchange := atomicScalarCompareExchange rmw.state manager layout byteRange false
    ({ size := size 1, kind := .u8 }) expect44 replacement false false .AcqRel .Acquire
  match exchange.outcome with
  | .ok result =>
    if !result.succeeded || result.oldValue.toUInt8 != .ok 44 then
      throw (IO.userError "successful compare-exchange returned the wrong result")
  | .error _ => throw (IO.userError "successful compare-exchange failed")
  if (← unwrap "compare-exchange memory read failed" (readByte exchange.state)) != 50 then
    throw (IO.userError "successful compare-exchange did not update allocation bytes")

  let failedExchange := atomicScalarCompareExchange exchange.state manager layout byteRange false
    ({ size := size 1, kind := .u8 }) expect44
    (Scalar.fromScalarInt (ScalarInt.ofUInt8 60)) false false .AcqRel .Acquire
  match failedExchange.outcome with
  | .ok result =>
    if result.succeeded || result.oldValue.toUInt8 != .ok 50 then
      throw (IO.userError "failed compare-exchange returned the wrong result")
  | .error _ => throw (IO.userError "failed compare-exchange could not validate latest read")
  if (← unwrap "failed compare-exchange memory read failed" (readByte failedExchange.state)) != 50 then
    throw (IO.userError "failed compare-exchange wrote the replacement scalar")
  if failedExchange.requiredHooks.contains .interpreterBeforeMemoryWrite then
    throw (IO.userError "failed compare-exchange requested a write hook")

  let weakSpurious := atomicScalarCompareExchange failedExchange.state manager layout
    byteRange false ({ size := size 1, kind := .u8 })
    (Scalar.fromScalarInt (ScalarInt.ofUInt8 50))
    (Scalar.fromScalarInt (ScalarInt.ofUInt8 61)) true true .Relaxed .Relaxed
  match weakSpurious.outcome with
  | .ok result =>
    if result.succeeded || result.oldValue.toUInt8 != .ok 50 then
      throw (IO.userError "weak compare-exchange did not honor its explicit spurious choice")
  | .error _ => throw (IO.userError "weak spurious compare-exchange validation failed")
  if (← unwrap "spurious compare-exchange memory read failed" (readByte weakSpurious.state)) != 50 then
    throw (IO.userError "spurious compare-exchange changed allocation bytes")
  IO.println "atomic-scalar:compare-exchange:success-failure-spurious:ok"

  -- A source validation error occurs after `write_scalar_atomic` has changed
  -- the allocation. Preserve that byte mutation in the returned error state.
  let badClockState := { initial with concurrency := {
    initial.concurrency with
      global := { initial.concurrency.global with weakMemory := false }
      allocation := VClockAlloc.newAllocation
        (ByteSize.ofU64 0 (by decide)) VTimestamp.ZERO mainIndex
      weakMemoryAllocation := none
  }}
  let failedAfterWrite := atomicScalarStore badClockState manager layout byteRange false
    (Scalar.fromScalarInt (ScalarInt.ofUInt8 99)) .Relaxed
  match failedAfterWrite.outcome with
  | .error (.dispatch (.validation .outOfBounds)) => pure ()
  | _ => throw (IO.userError "invalid detector range was not reported after the write")
  if (← unwrap "post-error allocation read failed" (readByte failedAfterWrite.state)) != 99 then
    throw (IO.userError "atomic validation failure discarded the preceding memory write")
  IO.println "atomic-scalar:post-write-validation-error:bytes-preserved"

  -- A malformed weak-memory allocation payload is an invariant failure before
  -- the write, not an accidental successful fallback.
  let missingBuffers := { initial with concurrency := {
    initial.concurrency with weakMemoryAllocation := none
  }}
  let rejected := atomicScalarStore missingBuffers manager layout byteRange false
    (Scalar.fromScalarInt (ScalarInt.ofUInt8 77)) .Relaxed
  match rejected.outcome with
  | .error .missingWeakMemoryAllocation => pure ()
  | _ => throw (IO.userError "missing weak-memory allocation was treated as success")
  if (← unwrap "rejected allocation read failed" (readByte rejected.state)) != 1 then
    throw (IO.userError "missing weak-memory state mutated scalar allocation bytes")
  IO.println "atomic-scalar:missing-buffer:rejected-before-write"
