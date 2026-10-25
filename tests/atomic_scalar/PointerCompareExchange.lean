import Miri.Concurrency.AtomicScalarMemory

open Miri.ABI Miri.Concurrency Miri.Interpreter Miri.Memory

private def bytes (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def ix : VectorIdx := VectorIdx.ofU32 0 (by decide)
private def id1 : AllocId := ⟨1, by decide⟩
private def id2 : AllocId := ⟨2, by decide⟩
private def pointer (layout : TargetDataLayout) (address : Nat) (id : AllocId) : Scalar Provenance :=
  Scalar.fromPointer layout ⟨bytes address, .concrete id BorTag.one⟩
private def require (message : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError message)
private def unwrap {E A : Type} (message : String) : Except E A → IO A
  | .ok a => pure a
  | .error _ => throw (IO.userError message)

private def fixture (layout : TargetDataLayout) (weakMemory : Bool)
    (value : Scalar Provenance) : IO (AtomicScalarMemory Provenance) := do
  let n := layout.pointerWidth.bits.toNat / 8
  let range : AllocRange := ⟨Size.ZERO, bytes n⟩
  let memory ← unwrap "allocation" (Allocation.fromBytes (Array.replicate n 0) Align.ONE .Mut)
  let memory ← match Allocation.writeScalar layout range value memory with
    | .ok () memory => pure memory
    | .error _ _ => throw (IO.userError "initial pointer write")
  pure { memory, concurrency := {
    global := { GlobalState.initial false weakMemory with multiThreaded := true }
    allocation := VClockAlloc.newAllocation (ByteSize.ofU64 n (by dsimp [n]; cases layout.pointerWidth <;> simp [PointerWidth.bits])) VTimestamp.ZERO ix
    weakMemoryAllocation := if weakMemory then some
      ((StoreBufferAlloc.newAllocation : StoreBufferAlloc (Scalar Provenance))
        |>.getOrCreateStoreBuffer range (some value)).allocation else none } }

private def widthIs32 (layout : TargetDataLayout) : Bool := layout.pointerWidth == .w32

private def check (layout : TargetDataLayout) (weakMemory : Bool) (address expectedAddress : Nat)
    (oldPointer : Bool) (expectedStyle : Nat) (weak spurious : Bool) : IO Unit := do
  let n := layout.pointerWidth.bits.toNat / 8
  let range : AllocRange := ⟨Size.ZERO, bytes n⟩
  let old ← if oldPointer then pure (pointer layout address id1)
    else unwrap "old integer representation" (Scalar.fromUInt (BitVec.ofNat 128 address) (bytes n))
  -- Equality ignores both allocation identity and borrow tag; storage does not.
  let expected ← if expectedStyle == 1 then
      pure (Scalar.fromPointer layout ⟨bytes expectedAddress, .concrete id1 ⟨2, by decide⟩⟩)
    else if expectedStyle == 2 then pure (pointer layout expectedAddress id2)
    else unwrap "integer pointer representation" (Scalar.fromUInt (BitVec.ofNat 128 expectedAddress) (bytes n))
  let replacement := pointer layout 8192 id2
  let initial ← fixture layout weakMemory old
  let result := atomicScalarCompareExchange initial (ThreadManager.initial false) layout range true
    { size := bytes n, kind := if widthIs32 layout then .u32 else .u64 } expected replacement weak spurious .AcqRel .Acquire
  let value ← match result.outcome with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"pointer CAS failed: {reprStr error}")
  require "old provenance lost" (value.oldValue == old)
  let actual ← unwrap "post-CAS scalar read" (result.state.memory.readScalar layout range true)
  require "memory/provenance" (actual == (if value.succeeded then replacement else old))
  if weakMemory then
    let some buffers := result.state.concurrency.weakMemoryAllocation
      | throw (IO.userError "lost weak-memory allocation")
    let some handle ← unwrap "buffer lookup" (buffers.getStoreBuffer range)
      | throw (IO.userError "lost CAS buffer")
    require "buffer provenance" (handle.buffer.last.val == some actual)
    require "CAS modification order" (handle.buffer.entries.length == (if value.succeeded then 2 else 1))
    if !value.succeeded then
      require "failure did not record latest load" ((handle.buffer.last.loadInfo.timestampFor? ix).isSome)
  require "flag window leaked" (!result.state.concurrency.global.ongoingActionDataRaceFree)
  require "write hook ordering" (result.requiredHooks ==
    [.atomicAccessCheck, .interpreterBeforeMemoryRead] ++
      (if value.succeeded then [.interpreterBeforeMemoryWrite] else []))
  match result.asOperationalOutcome with
  | .blocked (.interpreterHooks _) => pure ()
  | _ => throw (IO.userError "component CAS certified full execution")
  IO.println (if value.succeeded then "true" else "false")

private def errorStates (weakMemory : Bool) : IO Unit := do
  let layout : TargetDataLayout := ⟨.little, .w64⟩
  let range : AllocRange := ⟨Size.ZERO, bytes 8⟩
  let old := pointer layout 4096 id1
  let replacement := pointer layout 8192 id2
  let initial ← fixture layout weakMemory old
  let broken := { initial with concurrency := { initial.concurrency with
    allocation := VClockAlloc.newAllocation (ByteSize.ofU64 0 (by decide)) VTimestamp.ZERO ix } }
  for isEqual in [true, false] do
    let expected := pointer layout (if isEqual then 4096 else 4097) id2
    let result := atomicScalarCompareExchange broken (ThreadManager.initial false) layout range true
      { size := bytes 8, kind := .u64 } expected replacement false false .Relaxed .Relaxed
    match result.outcome with
    | .error (.dispatch (.validation .outOfBounds)) => pure ()
    | _ => throw (IO.userError "expected post-access detector failure")
    let actual ← unwrap "error scalar read" (result.state.memory.readScalar layout range true)
    require "error state lost source-ordered mutation" (actual == (if isEqual then replacement else old))
    require "error leaked flag" (!result.state.concurrency.global.ongoingActionDataRaceFree)
    require "error write hook" (result.requiredHooks.contains .interpreterBeforeMemoryWrite == isEqual)
    if weakMemory then
      let some buffers := result.state.concurrency.weakMemoryAllocation
        | throw (IO.userError "error lost buffer allocation")
      let some handle ← unwrap "error buffer lookup" (buffers.getStoreBuffer range)
        | throw (IO.userError "error lost buffer")
      require "validation error changed buffer before its source stage"
        (handle.buffer.entries.length == 1 && handle.buffer.last.val == some old)
  let malformed ← unwrap "malformed expected scalar" (Scalar.fromUInt 4096 (bytes 4))
  let invalid := atomicScalarCompareExchange initial (ThreadManager.initial false) layout range true
    { size := bytes 8, kind := .u64 } malformed replacement false false .Relaxed .Relaxed
  match invalid.outcome with
  | .error (.scalar _) => pure ()
  | _ => throw (IO.userError "pointer expected-size error accepted")
  require "comparison error wrote memory" ((← unwrap "comparison error read" (invalid.state.memory.readScalar layout range true)) == old)
  require "comparison error requested write" (!invalid.requiredHooks.contains .interpreterBeforeMemoryWrite)

  let wrongNew := atomicScalarCompareExchange initial (ThreadManager.initial false) layout range true
    { size := bytes 8, kind := .u64 } old malformed false false .Relaxed .Relaxed
  match wrongNew.outcome with
  | .error (.allocation (.scalar _)) => pure ()
  | _ => throw (IO.userError "wrong-size write was accepted")
  require "write error changed old provenance" ((← unwrap "write error read" (wrongNew.state.memory.readScalar layout range true)) == old)
  require "write error lost write obligation" (wrongNew.requiredHooks.contains .interpreterBeforeMemoryWrite)
  let uninitMemory ← match Allocation.writeUninit range (bytes 8) initial.memory with
    | .ok () memory => pure memory
    | .error _ _ => throw (IO.userError "uninit fixture")
  let unreadable := atomicScalarCompareExchange { initial with memory := uninitMemory }
    (ThreadManager.initial false) layout range true
    { size := bytes 8, kind := .u64 } old replacement false false .Relaxed .Relaxed
  match unreadable.outcome with
  | .error (.allocation _) => pure ()
  | _ => throw (IO.userError "uninitialized read accepted")
  require "read error attempted write" (!unreadable.requiredHooks.contains .interpreterBeforeMemoryWrite)
  require "read error leaked window" (!unreadable.state.concurrency.global.ongoingActionDataRaceFree)

private def relativePointerRejected : IO Unit := do
  let layout : TargetDataLayout := ⟨.little, .w64⟩
  let range : AllocRange := ⟨Size.ZERO, bytes 8⟩
  let provenance ← unwrap "CTFE provenance" (CtfeProvenance.fromAllocId id1)
  let old : Scalar CtfeProvenance := Scalar.fromPointer layout ⟨bytes 4096, provenance⟩
  let memory ← unwrap "relative allocation" (Allocation.fromBytes (Array.replicate 8 0) Align.ONE .Mut)
  let memory ← match Allocation.writeScalar layout range old memory with
    | .ok () memory => pure memory
    | .error _ _ => throw (IO.userError "relative write")
  let initial : AtomicScalarMemory CtfeProvenance := { memory, concurrency := {
    global := GlobalState.initial false false
    allocation := VClockAlloc.newAllocation (ByteSize.ofU64 8 (by decide)) VTimestamp.ZERO ix
    weakMemoryAllocation := none } }
  let result := atomicScalarCompareExchange initial (ThreadManager.initial false) layout range true
    { size := bytes 8, kind := .u64 } old old false false .Relaxed .Relaxed
  match result.outcome with
  | .error (.scalar .readPointerAsInt) => pure ()
  | _ => throw (IO.userError "relative offset was treated as address")
  require "relative comparison wrote" (!result.requiredHooks.contains .interpreterBeforeMemoryWrite)
  require "relative comparison changed memory" ((← unwrap "relative read" (result.state.memory.readScalar layout range true)) == old)

-- Source-expression differential driver supplies the expected success booleans;
-- the assertions above additionally check actual allocation/provenance and errors.
def main : IO Unit := do
  for width in [PointerWidth.w32, PointerWidth.w64] do
    for endian in [Endian.little, Endian.big] do
      for weakMemory in [false, true] do
        for address in [0, 4096] do
          for expectedAddress in [0, 4096, 4097] do
            for oldPointer in [false, true] do
              for expectedStyle in [0, 1, 2] do
                for weak in [false, true] do
                  for spurious in [false, true] do
                    check ⟨endian, width⟩ weakMemory address expectedAddress oldPointer expectedStyle weak spurious
  errorStates false
  errorStates true
  relativePointerRejected
