import Miri.Interpreter.MachineHooks
open Miri Miri.ABI Miri.Memory Miri.Interpreter
open Miri.Concurrency
open Miri.TreeBorrows
open Miri.TreeBorrows.RetagPolicy
open Miri.Interpreter.MachineHooks

def allocId : AllocId := ⟨1, by decide⟩
def rootTag : BorTag := ⟨1, by decide⟩
def layout : LocalLayout := ⟨0, {
  fields := .Primitive, variants := .Single 0, backendRepr := .Memory (sized := true),
  largestNiche := none, uninhabited := false, align := .new Align.ONE,
  size := Size.ofBytes 1, maxReprAlign := none, unadjustedAbiAlign := Align.ONE,
  reprC := false, randomizationSeed := 0 }⟩
def place : MPlaceTy Provenance := ⟨⟨⟨Size.ZERO, some (.concrete allocId rootTag)⟩, .none, none⟩, layout⟩
def fixtureBodies : Array MIR.Body := #[⟨.Built, 0, none, #[layout.ty, layout.ty], #[]⟩]
def fixtureLoaded : LoadedBody := ⟨BodyIdentity.ofCanonicalIndex 0, fixtureBodies[0]⟩
def fixtureIdentity : LocalsIdentity := (LocalsIdentitySupply.allocate ⟨0⟩).2
def frame : Frame Provenance LocalLayout MachineHooks.FrameExtra :=
  { body := fixtureLoaded.body
    bodyIdentity := fixtureLoaded.identity
    localsIdentity := fixtureIdentity
    functionInstance := ⟨.Item 0, #[]⟩
    extra := { borrowTracker := some {}, catchUnwind := none, userRelevance := 0, dataRace := some {} }
    returnContinuation := .stop true
    returnPlace := .memory ⟨place.mplace, layout⟩
    locals := #[⟨.dead, some layout⟩, ⟨.dead, some layout⟩]
    vaList := #[], trackCallerArg := none, location := .unwinding ⟨0⟩ }
def idx : VectorIdx := .ofU32 0 (by decide)
def timestamp (n : Nat) : IO VTimestamp :=
  match VTimestamp.ofTime n with
  | .ok value => pure value
  | .error _ => throw (IO.userError "timestamp")
def initial : IO (MachineHooks.State Unit (List String)) := do
  let .ok allocation := Allocation.fromBytes (Prov := Provenance) #[7] Align.ONE .Mut
    | throw (IO.userError "allocation")
  let memory0 := MemoryState.setIssuedIds
    (MemoryState.empty : MemoryState Provenance BorrowTree Unit) #[allocId]
  let memory : MemoryState Provenance BorrowTree Unit := {memory0 with
    live := #[(allocId, ⟨.stack, allocation.withExtra (BorrowTree.new rootTag (Size.ofBytes 1))⟩)]}
  let global := { Miri.Concurrency.GlobalState.initial false false with
    multiThreaded := true
    vectorClocks := [{ clock := VClock.newWithIndex idx (← timestamp 3) }] }
  return ⟨⟨#[frame]⟩, ⟨memory, some ⟨{ Miri.TreeBorrows.GlobalState.new with nextPointerTag := ⟨2, by decide⟩ }, .Default⟩,
    some global, ThreadManager.initial false,
    #[(allocId, VClockAlloc.newAllocation (ByteSize.ofU64 1 (by decide)) (← timestamp 9) idx)], #[], []⟩⟩
def blocked (message : String) : MachineHooks.M Unit (List String) A := throw (.unsupported message)
def storage : MachineHooks.StorageHooks Unit (List String) := {
  veryTriviallySized := fun _ => .ok true
  layout := fun _ => blocked "unused layout query"
  allocateDyn := fun _ _ => blocked "unused dynamic allocation"
  deallocateStack := fun _ => blocked "unused local deallocation" }
def check (ok : Bool) (message : String) : IO Unit :=
  unless ok do throw (IO.userError message)
def request : RetagPipeline.Request := {
  typeShape := .reference, typeFacts := ⟨true, true, true⟩, referenceKind := .Mutable
  mode := .FnEntry, config := ⟨false, false⟩, layoutSize := Size.ofBytes 1
  originalProvenance := place.mplace.ptr.provenance
  pointeeIsFreeze := true, preciseInteriorMut := false
  hooks := {
    placeConversion := .ok (), sizeAndAlignOfValue := .ok none, pointerAccess := .ok ()
    allocationResolution := some ⟨allocId, Size.ZERO, .concrete rootTag⟩
    creationLog := .ok (), freezeVisitor := .error "precise interior mutability disabled"
    allocationExtra := .ok (), dataRace := none } }

/-- Fixture writes use real Tree Borrows access and Allocation.writeUninit.
The pointer is known one-byte, in-bounds and concrete in this fixture only. -/
def writeUninit (protectedPlace : MPlaceTy Provenance) : MachineHooks.M Unit (List String) Unit := do
  let some (.concrete id tag) := protectedPlace.mplace.ptr.provenance | throw (.invalidProgram "provenance")
  MachineHooks.memoryRaceWrite id (allocRange Size.ZERO (Size.ofBytes 1)) .Write
  let state ← get
  let some (_, entry) := state.machine.memory.live.find? fun e => e.1 == id | throw (.invalidProgram "allocation")
  let some tracker := state.machine.borrowTracker | throw (.invalidProgram "tracker")
  let accessed := entry.allocation.extra.performBorrowAccessRange (.concrete tag) Size.ZERO (Size.ofBytes 1)
    .Write tracker.global.protectedTags .VisitChildrenOfAccessed
  let allocation := entry.allocation.setExtra accessed.tree
  let .ok memory := state.machine.memory.setLiveAllocation id allocation | throw (.invalidProgram "tree update")
  set { state with machine := { state.machine with memory, user := state.machine.user ++ ["uninit"] } }
  unless accessed.status == .Completed do throw (.undefinedBehavior "protected write")
  let changed := Allocation.writeUninit (allocRange Size.ZERO (Size.ofBytes 1)) (Size.ofBytes 8) allocation
  let updated := match changed with | .ok _ allocation | .error _ allocation => allocation
  let .ok memory := memory.setLiveAllocation id updated | throw (.invalidProgram "uninit update")
  modify fun s => { s with machine := { s.machine with memory } }
  match changed with
  | .ok _ _ => pure ()
  | .error _ _ => throw (.invalidProgram "uninit failure")
def hooks : MachineHooks.Hooks Unit (List String) := {
  preparePointerRetag := fun _ _ _ => pure request
  reconstructImmediate := fun _ _ => blocked "reconstructImmediate not needed"
  preparePlaceProtection := fun _ => pure request
  writeUninit
  ensureTreeExtra := fun id => do
    let state ← get
    unless state.machine.memory.live.any (fun e => e.1 == id) do throw (.invalidProgram "missing extra") }

def main : IO Unit := do
  let start ← initial
  let (state, result) := MachineHooks.run (MachineHooks.storageLiveDyn storage 1 .none) start
  check result.isOk "storage live"
  let some current := state.stack.currentFrame? | throw (IO.userError "frame")
  let some clocks := current.extra.dataRace | throw (IO.userError "clocks")
  check ((clocks.get 1).write.time == 3 && clocks.localClocks.size == 1) "FrameExtra write clocks survive storage live"
  let localRead := MachineHooks.localAccessAfterRead current state.machine 1
  let .ok () := localRead.outcome | throw (IO.userError "local read")
  let some clocks := localRead.frame.extra.dataRace | throw (IO.userError "clocks")
  check ((clocks.get 1).read.time == 3) "LocalAccess read updates FrameExtra"
  let state := { state with stack := ⟨#[localRead.frame]⟩, machine := localRead.state }
  let (state, result) := MachineHooks.run
    (MachineHooks.afterLocalMovedToMemory 1 place (fun _ _ => pure ⟨7⟩)) state
  check result.isOk "materialize"
  let some current := state.stack.currentFrame? | throw (IO.userError "frame")
  let some clocks := current.extra.dataRace | throw (IO.userError "clocks")
  let some (_, allocation) := state.machine.raceAllocations[0]? | throw (IO.userError "race allocation")
  let .ok cell := allocation.cellAt 0 | throw (IO.userError "cell")
  check (clocks.localClocks.isEmpty && cell.write.2.time == 3 && (cell.read.index idx).time == 3) "machine materialization transfers historical clocks"
  check (state.machine.allocationSpans[0]?.map (·.2.1) == some ⟨7⟩) "declaration span recorded"
  let materializedState := state
  let failing : MachineHooks.M Unit (List String) Unit := do
    modify fun s => { s with machine := { s.machine with user := ["body"] } }
    throw (.unsupported "body")
  let (state, result) := MachineHooks.run (MachineHooks.withRetagMode .FnEntry failing) start
  check (!result.isOk && state.machine.borrowTracker.map (·.retagMode) == some .Default && state.machine.user == ["body"]) "mode restored after error, body effects retained"
  let raceIndex := VectorIdx.ofU32 1 (by decide)
  let raceThread := ThreadId.ofU32 1 (by decide)
  let some racyGlobal := start.machine.dataRace | throw (IO.userError "global")
  let racyGlobal := { racyGlobal with
    vectorClocks := racyGlobal.vectorClocks ++ [{ clock := VClock.newWithIndex raceIndex (← timestamp 5) }]
    vectorInfo := racyGlobal.vectorInfo ++ [raceThread]
    threadInfo := racyGlobal.threadInfo ++ [⟨some raceIndex, none⟩] }
  let racy := { start with machine := { start.machine with
    dataRace := some racyGlobal
    threads := { start.machine.threads with threads := start.machine.threads.threads ++ [ThreadRecord.initial none none] }
    raceAllocations := #[(allocId, VClockAlloc.newAllocation (ByteSize.ofU64 1 (by decide)) (← timestamp 5) raceIndex)] } }
  let (unknown, result) := MachineHooks.run (MachineHooks.protectInPlaceFunctionArgument hooks place) racy
  check (result == .error (.undefinedBehavior "DataRace")) "concurrent retag reports actual memory race"
  let some unknownTracker := unknown.machine.borrowTracker | throw (IO.userError "tracker")
  let some (_, unknownAlloc) := unknown.machine.memory.live[0]? | throw (IO.userError "allocation")
  check (unknownTracker.global.nextPointerTag.value == 3 && unknownTracker.global.protectedTags.size == 1 &&
    (unknownAlloc.allocation.extra.indexOfTag ⟨2, by decide⟩).isNone && unknown.machine.user.isEmpty)
    "failed retag preserves source prefix, stops before child insert and uninit"
  let some concurrentGlobal := start.machine.dataRace | throw (IO.userError "global")
  let concurrentGlobal := { concurrentGlobal with vectorClocks := [{ clock := VClock.newWithIndex idx (← timestamp 9) }] }
  let concurrent := { start with machine := { start.machine with dataRace := some concurrentGlobal } }
  let pointerLayout : LocalLayout := ⟨1, { layout.layout with
    size := Size.ofBytes 8
    backendRepr := .Scalar (.Initialized (value := .Pointer .ZERO)
      (validRange := ⟨BitVec.ofNat 128 1, BitVec.ofNat 128 (2^64 - 1)⟩)) }⟩
  let .ok pointerScalar := Scalar.fromMaybePointer ⟨.little, .w64⟩ place.mplace.ptr
    | throw (IO.userError "pointer scalar")
  let pointerValue : RvalueImmTy Provenance := ⟨.scalar pointerScalar, pointerLayout⟩
  let pointerHooks := { hooks with reconstructImmediate := fun value provenance => do
    let .ok scalar := Scalar.fromMaybePointer ⟨.little, .w64⟩ { place.mplace.ptr with provenance }
      | throw (.invalidProgram "pointer reconstruction")
    pure { value with imm := .scalar scalar } }
  let (pointerState, pointerResult) := MachineHooks.run
    (MachineHooks.withRetagMode .FnEntry (MachineHooks.retagPtrValue pointerHooks pointerValue 1)) concurrent
  let .ok (some retaggedPointer) := pointerResult | throw (IO.userError "retag_ptr_value")
  let .scalar retaggedScalar := retaggedPointer.imm | throw (IO.userError "retag scalar")
  let .ok retaggedPtr := retaggedScalar.toPointer ⟨.little, .w64⟩ | throw (IO.userError "retag pointer")
  check (retaggedPtr.provenance == some (.concrete allocId ⟨2, by decide⟩) && retaggedPointer.layout == pointerLayout)
    "retag_ptr_value reconstructs typed pointer with new protected tag"
  let some (_, pointerClocks) := pointerState.machine.raceAllocations[0]? | throw (IO.userError "clocks")
  let .ok pointerCell := pointerClocks.cellAt 0 | throw (IO.userError "cell")
  check ((pointerCell.read.index idx).readType == .Retag && (pointerCell.read.index idx).time == 9)
    "retag_ptr_value reads update actual clocks"
  let (concurrentProtected, result) := MachineHooks.run (MachineHooks.protectInPlaceFunctionArgument hooks place) concurrent
  check result.isOk "concurrent retag completes with actual clocks"
  let some (_, protectedClocks) := concurrentProtected.machine.raceAllocations[0]? | throw (IO.userError "clocks")
  let .ok protectedCell := protectedClocks.cellAt 0 | throw (IO.userError "cell")
  check (protectedCell.write.2.time == 9 && protectedCell.writeType == .Write)
    "uninit performs real memory write after retag read"
  let singleGlobal := { concurrentGlobal with multiThreaded := false }
  let singleThread := { start with machine := { start.machine with dataRace := some singleGlobal } }
  let (singleThread, result) := MachineHooks.run (MachineHooks.protectInPlaceFunctionArgument hooks place) singleThread
  let some (_, singleAllocation) := singleThread.machine.raceAllocations[0]? | throw (IO.userError "single allocation")
  let .ok singleCell := singleAllocation.cellAt 0 | throw (IO.userError "single cell")
  check (result.isOk && singleCell.writeType == .Allocate && singleCell.write.2.time == 9)
    "configured detector's source single-thread guard skips clocks while TB and uninit proceed"
  -- Disable vector clocks for the retag fixture: source has no race leaf in this mode.
  let borrowOnly := { start with
    machine := { start.machine with dataRace := none }
    stack := ⟨#[{ frame with extra := { frame.extra with dataRace := none } }]⟩ }
  let (state, result) := MachineHooks.run (MachineHooks.protectInPlaceFunctionArgument hooks place) borrowOnly
  check result.isOk "protected argument"
  let some tracker := state.machine.borrowTracker | throw (IO.userError "tracker")
  check (tracker.global.protectedTags.size == 1 && state.machine.user == ["uninit"]) "strong protection precedes real uninit write"
  let (afterPop, result) := MachineHooks.run (MachineHooks.beforeStackPop hooks) state
  check result.isOk "protector release"
  let some tracker := afterPop.machine.borrowTracker | throw (IO.userError "tracker")
  check (tracker.global.protectedTags.size == 0) "protectors removed after tree release"
  let some (_, entry) := afterPop.machine.memory.live[0]? | throw (IO.userError "allocation")
  let read := Allocation.readScalar entry.allocation ⟨.little, .w64⟩ (allocRange Size.ZERO (Size.ofBytes 1)) false
  check (!read.isOk) "protected source contents remain uninitialized after pop"
  let secondId := ThreadId.ofU32 1 (by decide)
  let secondIndex := VectorIdx.ofU32 1 (by decide)
  let some raceGlobal := materializedState.machine.dataRace | throw (IO.userError "race global")
  let secondClock := (VClock.newWithIndex idx (← timestamp 2)).join
    (VClock.newWithIndex secondIndex (← timestamp 4))
  let raceGlobal := { raceGlobal with
    threadInfo := raceGlobal.threadInfo ++ [⟨some secondIndex, none⟩]
    vectorInfo := raceGlobal.vectorInfo ++ [secondId]
    vectorClocks := raceGlobal.vectorClocks ++ [{ clock := secondClock }] }
  let racingMachine := { materializedState.machine with
    dataRace := some raceGlobal
    threads := { materializedState.machine.threads with
      activeThread := secondId
      threads := materializedState.machine.threads.threads ++ [ThreadRecord.initial none none] } }
  let (_, result) := MachineHooks.memoryRaceAccess racingMachine allocId
    (allocRange Size.ZERO (Size.ofBytes 1)) none .Read
  check (result == .error (.undefinedBehavior "DataRace")) "second thread sees materialized local write race"
  let syncedClock := (VClock.newWithIndex idx (← timestamp 3)).join
    (VClock.newWithIndex secondIndex (← timestamp 4))
  let synced := { racingMachine with dataRace := some { raceGlobal with
    vectorClocks := raceGlobal.vectorClocks.set 1 { clock := syncedClock } } }
  let (synced, result) := MachineHooks.memoryRaceAccess synced allocId
    (allocRange Size.ZERO (Size.ofBytes 1)) none .Read
  check result.isOk "synchronized second-thread materialized read"
  let some (_, allocation) := synced.raceAllocations[0]? | throw (IO.userError "race allocation")
  let .ok cell := allocation.cellAt 0 | throw (IO.userError "cell")
  check ((cell.read.index secondIndex).time == 4) "memory read updates actual shared allocation clocks"
  let .ok indirectFrame := frame.replaceLocalValue 1 (.live (.indirect place.mplace))
    | throw (IO.userError "indirect frame")
  let indirectStart := { start with stack := ⟨#[indirectFrame]⟩ }
  let (failedLive, result) := MachineHooks.run (MachineHooks.storageLiveDyn storage 1 .none) indirectStart
  let some failedFrame := failedLive.stack.currentFrame? | throw (IO.userError "frame")
  let .ok slot := failedFrame.getLocal 1 | throw (IO.userError "local")
  let some failedClocks := failedFrame.extra.dataRace | throw (IO.userError "clocks")
  check (!result.isOk && slot.value == .live (.immediate .uninit) && (failedClocks.get 1).write.time == 3)
    "replacement and local-clock updates survive old-allocation deallocation failure"
  let absentId : AllocId := ⟨2, by decide⟩
  let absentPlace := { place with mplace := { place.mplace with ptr :=
    ⟨Size.ZERO, some (.concrete absentId rootTag)⟩ } }
  let (failedMove, result) := MachineHooks.run
    (MachineHooks.afterLocalMovedToMemory 1 absentPlace (fun _ _ => pure ⟨19⟩)) materializedState
  check (!result.isOk && failedMove.machine.allocationSpans.any (fun e => e.1 == absentId && e.2.1 == ⟨19⟩))
    "span registration survives subsequent allocation-extra failure"
  let some protectedFrame := state.stack.currentFrame? | throw (IO.userError "frame")
  let some borrowFrame := protectedFrame.extra.borrowTracker | throw (IO.userError "borrow frame")
  let some tracker := state.machine.borrowTracker | throw (IO.userError "tracker")
  let absentTag : BorTag := ⟨3, by decide⟩
  let updatedBorrowFrame := borrowFrame.addProtector absentId absentTag
  let updatedFrame := { protectedFrame with extra := { protectedFrame.extra with borrowTracker := some updatedBorrowFrame } }
  let updatedGlobal := { tracker.global with protectedTags := tracker.global.protectedTags.insert absentTag .StrongProtector }
  let failingPop := { state with
    stack := ⟨#[updatedFrame]⟩
    machine := { state.machine with borrowTracker := some { tracker with global := updatedGlobal } } }
  let (failedPop, result) := MachineHooks.run (MachineHooks.beforeStackPop hooks) failingPop
  let some failedTracker := failedPop.machine.borrowTracker | throw (IO.userError "tracker")
  check (!result.isOk && failedTracker.global.protectedTags.size == 2)
    "later release failure does not remove any global protector"
  IO.println "connected machine hooks passed"
