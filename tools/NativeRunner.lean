import Miri.Input.EvalSourceRunFinalization
import Miri.Input.ExecutionChoicePolicy
import Miri.Input.CompilerMiriEntry
import Miri.Input.NativeMathHost

/-! Standalone source run harness draft. It enters through
EvalSourceRunFinalization.runFromSourceAndFinalize. Host operations that this
fixture cannot perform remain demand-local Unsupported outcomes. -/
open Lean Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

private abbrev Os := ByteArray
private abbrev R := Unit
private abbrev Payload := Input.EvalSyncObjectAccess.Payload
private abbrev H := Unit
private abbrev D := Unit
private abbrev Aff := CpuAffinity.Mask
private abbrev B := Unit
private abbrev Poll := Unit
private abbrev Instant := Unit
private abbrev System := Unit
private abbrev Native := Unit
private abbrev Profiler := Unit
private abbrev Raw := Unit
private abbrev Listener := Unit
private abbrev TcpStream := Unit
private abbrev Error := Unit
private abbrev Other := Input.EvalUnixSourceConstruction.Other Raw Listener TcpStream Error
private abbrev Host := Input.EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler
private abbrev CoreUser := Input.EvalCoreMachine.User Os R Payload H D Other Aff B Host
private abbrev OuterState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Outer
    (Input.EvalWorld.World Os R Payload H D Other Aff B Host))
private abbrev CoreOptions := Input.EvalConfigurationCore.Options

private def unavailable {S A : Type} (name : String) : EStateM StepError S A :=
  throw (.unsupported s!"native fixture has no {name} capability")

private def must {A : Type} (value : Except String A) : IO A :=
  match value with
  | .ok result => pure result
  | .error reason => throw (IO.userError reason)

private def options : CoreOptions := {
  place := {debugAssertions := false, dynamicFuel := 256, validation := .Shallow}
  limits := {callDispatch := 128, casts := 128, retag := 128, validation := 128}
  compatibilityBudget := 128, varArgsBudget := 128, callbackCapacity := 128
  floatNondeterministic := false, weakFailureRate := 0, crossCrateInlineAlways := false
  userRelevantCrates := #[], ignoreOptionalOverflowChecks := false, panicUnwinds := false
  retag := {implicitWrites := false, preciseInteriorMut := true} }

/-- Explicit UI-comparison configuration; ordinary diagnostic runs retain their defaults. -/
private structure UiSettings where
  source : String
  validation : ValidityMachine.ValidationMode := .Shallow
  alignment : ValidityMachine.AlignmentCheck := .Int
  provenance : Miri.Memory.AllocAddresses.ProvenanceMode := .default
  treeBorrows : Bool := true
  preciseInteriorMut : Bool := true
  implicitWrites : Bool := false
  dataRace : Bool := true
  weakMemory : Bool := true
  fixedScheduling : Bool := false
  deterministicConcurrency : Bool := false
  ignoreLeaks : Bool := false

private def uiSettings (source flags : String) : Except String UiSettings := do
  let values ← (← Json.parse flags).getArr?
  let mut ui : UiSettings := {source}
  for value in values do
    let flag ← value.getStr?
    ui ← match flag with
      | "-Zmiri-tree-borrows" => pure {ui with treeBorrows := true, preciseInteriorMut := true, implicitWrites := false}
      | "-Zmiri-disable-stacked-borrows" => pure {ui with treeBorrows := false}
      | "-Zmiri-tree-borrows-implicit-writes" =>
        unless ui.treeBorrows do throw "implicit writes requires Tree Borrows"
        pure {ui with implicitWrites := true}
      | "-Zmiri-tree-borrows-no-precise-interior-mut" =>
        unless ui.treeBorrows do throw "precise interior mutability setting requires Tree Borrows"
        pure {ui with preciseInteriorMut := false}
      | "-Zmiri-disable-validation" => pure {ui with validation := .No}
      | "-Zmiri-recursive-validation" => pure {ui with validation := .Deep}
      | "-Zmiri-disable-alignment-check" => pure {ui with alignment := .None}
      | "-Zmiri-symbolic-alignment-check" => pure {ui with alignment := .Symbolic}
      | "-Zmiri-strict-provenance" => pure {ui with provenance := .strict}
      | "-Zmiri-permissive-provenance" => pure {ui with provenance := .permissive}
      | "-Zmiri-ignore-leaks" => pure {ui with ignoreLeaks := true}
      | "-Zmiri-fixed-schedule" => pure {ui with fixedScheduling := true}
      | "-Zmiri-disable-data-race-detector" => pure {ui with dataRace := false, weakMemory := false}
      | "-Zmiri-deterministic-concurrency" => pure {ui with fixedScheduling := true, deterministicConcurrency := true, weakMemory := false}
      | _ => throw s!"unsupported UI runtime setting: {flag}"
  pure ui

private def uiOptions (ui : UiSettings) : CoreOptions :=
  { options with
    place := {options.place with validation := ui.validation}
    floatNondeterministic := true
    collectLeakBacktraces := !ui.ignoreLeaks
    weakFailureRate := if ui.deterministicConcurrency then 0 else 0x3fe999999999999a
    retag := {implicitWrites := ui.implicitWrites, preciseInteriorMut := ui.preciseInteriorMut} }

private def uiProfile (ui : UiSettings) : Json := Json.mkObj [
  ("num_cpus", toJson (1 : Nat)), ("environment_policy", toJson ("empty" : String)),
  ("argv0", toJson ui.source), ("rng_seed", toJson (0 : Nat)),
  ("choice_policy", toJson ("seeded-generated-0" : String)),
  ("borrow_tracker", toJson (if ui.treeBorrows then "tree_borrows" else "none" : String)),
  ("tree_borrows", if ui.treeBorrows then Json.mkObj [
    ("precise_interior_mut", toJson ui.preciseInteriorMut), ("implicit_writes", toJson ui.implicitWrites)] else .null),
  ("validation", toJson (match ui.validation with | .No => "No" | .Shallow => "Shallow" | .Deep => "Deep")),
  ("alignment_check", toJson (match ui.alignment with | .None => "None" | .Symbolic => "Symbolic" | .Int => "Int")),
  ("provenance_mode", toJson (match ui.provenance with | .default => "Default" | .strict => "Strict" | .permissive => "Permissive")),
  ("data_race_detector", toJson ui.dataRace), ("weak_memory_emulation", toJson ui.weakMemory),
  ("fixed_scheduling", toJson ui.fixedScheduling), ("ignore_leaks", toJson ui.ignoreLeaks),
  ("collect_leak_backtraces", toJson (uiOptions ui).collectLeakBacktraces),
  ("genmc", toJson false), ("native_libraries", toJson (0 : Nat)),
  ("short_fd_operations", toJson true), ("float_nondeterminism", toJson true),
  ("cmpxchg_weak_failure_rate", toJson (if ui.deterministicConcurrency then (0.0 : _root_.Float) else 0.8)),
  ("address_reuse_cross_thread_rate", toJson (if ui.deterministicConcurrency then (0.0 : _root_.Float) else 0.1))]

private def choiceTape (seed : Option UInt64) (inputs : Array ExecutionChoices.Input) :=
  match seed with
  | none => Input.ExecutionChoicePolicy.unboundedDiagnosticTape inputs
  | some value => Input.ExecutionChoicePolicy.unboundedSeededDiagnosticTape value inputs

private def choiceMode (seed : Option UInt64) : String :=
  match seed with
  | none => "diagnostic-zero"
  | some value => s!"seeded-diagnostic seed={value.toNat} algorithm=SplitMix64-v1"

private def linuxOs : Input.EvalHostRuntimeConstruction.OsHostEffects Os := {
  hostWindows := false, hostUnix := true, targetWindows := false
  fromUnixBytes := id
  fromUtf8 := fun bytes => match String.fromUTF8? bytes with
    | some _ => .ok bytes
    | none => .error (.invalidProgram "invalid UTF-8 in Linux OS string")
  fromWide := fun _ => .error (.unsupported "wide OS strings are unavailable on this Linux host")
  toWide := fun _ => .error (.unsupported "wide OS strings are unavailable on this Linux host")
  encodedBytes := id
  encodedLength := fun value => value.size
  decodeUnixBytes := .ok
  empty := ByteArray.empty
  concat := fun left right => left ++ right
  ascii := fun text => text.toUTF8
  isEmpty := fun value => value.isEmpty
  containsEquals := fun value => value.data.contains 61 }

namespace NativeRunnerError
/-- Pinned core/io/error.rs `From<ErrorKind>` creates Repr::new_simple:
kind is retained and raw_os_error is None. The runner's host payload is Unit;
constructing this value requires no host I/O or numeric errno convention. -/
def fromKind (kind : IoError.ErrorKind) : IoError.HostError Unit :=
  {kind, raw := none, payload := ()}
end NativeRunnerError

private def unavailableIoError (os : String) : IoError.Hooks S Unit := {
  family := .unix, os, hostUnix := true
  hostErrno := fun _ => unavailable "host errno translation"
  libc := fun _ => unavailable "compiler libc errno conversion"
  windows := fun _ => unavailable "Windows error conversion"
  scalarI32 := fun _ => unavailable "host error scalar conversion"
  scalarU32 := fun _ => unavailable "host error scalar conversion"
  hostFromRaw := fun _ => unavailable "raw host error conversion"
  hostFromKind := fun kind => pure (NativeRunnerError.fromKind kind)
  getLastErrorPlace := unavailable "sync errno lookup"
  setLastErrorPlace := fun _ => unavailable "sync errno update"
  allocateU32Machine := unavailable "sync errno allocation"
  writeScalar := fun _ _ => unavailable "sync errno memory write"
  readScalar := fun _ => unavailable "sync errno memory read"
  writeInt := fun _ _ => unavailable "sync errno memory write" }

private def sourceLeaves (dummy : SpanRef) (geometry : Input.InitialMachine.Geometry)
    (pageSize : UInt64) (numCpus hostPid : UInt32) (uiMode : Bool) (alignment : ValidityMachine.AlignmentCheck) : Input.EvalConfigurationCore.SourceLeaves
    Os R Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
    Unit Unit ByteArray Miri.MIR.Place Unit Instant Payload Unit := {
  hostConfiguration := {
    communicate := false, muteOutput := true, hostUsizeBits := 64
    profileOutput := none, nativeLibraries := #[]
    hostTriple := "x86_64-unknown-linux-gnu", targetTriple := "x86_64-unknown-linux-gnu"
    nativeSupported := false
    control := ⟨0, 0x3f847ae147ae147b, true⟩ }
  nativeHost := none
  sync := Input.EvalSyncObjectAccess.onAccess
  storage := fun size _ => some (Array.replicate size.bytes.toNat 0)
  spans := ⟨dummy, false⟩
  foreignSource := {
    shortFdOperations := uiMode
    varArgsBudget := 256
    host := {
      hostOverflowChecks := true
      os := linuxOs
      environment := {
        invalidArgument := pure 22
        envVarNotFound := unavailable "host environment lookup" }
      unixConfig := {
        communicate := false, isolatedOp := .reject .abort
        hostPid := pure hostPid
        currentDirectory := unavailable "host current directory"
        setCurrentDirectory := fun _ => unavailable "host current-directory update"
        pageSize, numCpus, miriVersion := "0.1.0"
        homeDirectory := unavailable "host home directory"
        hostErrorDisplay := fun _ => unavailable "host error display"
        unknownErrorDisplay := fun _ => unavailable "unknown error display" }
      ioError := {
        hostErrno := fun _ => unavailable "host errno lookup"
        hostFromRaw := fun _ => unavailable "raw host error conversion"
        hostFromKind := fun kind => pure (NativeRunnerError.fromKind kind) }
      native := {call := fun _ _ _ => unavailable "native library call"}
      openFiles := {
        pathFromOs := id
        isAbsolute := fun path => path.data[0]? == some 47
        isEmpty := fun path => path.isEmpty
        isDot := fun path => path.data == #[46]
        emptyPath := ByteArray.empty
        procAbsolute := fun _ => unavailable "host absolute-path query"
        diagnoseProc := unavailable "proc-path diagnostic"
        hostCustomFlag := fun _ => unavailable "host custom open flags"
        openFile := fun _ _ _ => unavailable "host file open"
        openDirectoryAsFile := fun _ _ _ => unavailable "host directory open"
        metadata := fun _ => unavailable "host file metadata"
        asDirectory := fun _ => unavailable "host directory conversion" }
      fileResources := {
        dropFile := fun _ => unavailable "host file cleanup"
        dropDirectory := fun _ => unavailable "host directory cleanup"
        dropOther := fun _ => unavailable "host Other-resource cleanup" }
      hostFiles := {
        hostRead := fun _ _ => unavailable "host file read"
        hostWrite := fun _ _ => unavailable "host file write"
        flushStdout := unavailable "host stdout flush"
        hostSeek := fun _ _ => unavailable "host file seek"
        hostMetadata := fun _ => unavailable "host file metadata"
        hostIsTerminal := fun _ => unavailable "host terminal query"
        permissionDenied := unavailable "host permission-denied error" }
      fileLocks := {
        tryLock := fun _ _ => unavailable "host file lock"
        unlock := fun _ => unavailable "host file unlock" }
      positional := {
        read := fun _ _ _ _ _ => unavailable "host positional read"
        write := fun _ _ _ _ _ => unavailable "host positional write" }
      control := {fullSync := fun _ => unavailable "host full sync"}
      socket := {
        newRaw := fun _ => unavailable "host socket creation"
        nonblocking := fun _ _ => unavailable "host socket mode"
        dropRaw := fun _ => unavailable "host socket cleanup"
        rawToListener := fun _ => unavailable "host listener conversion"
        rawToStream := fun _ => unavailable "host stream conversion"
        hostBind := fun _ _ => unavailable "host socket bind"
        hostListen := fun _ _ => unavailable "host socket listen"
        hostConnect := fun _ _ => unavailable "host socket connect"
        hostAccept := fun _ => unavailable "host socket accept"
        hostSend := fun _ _ => unavailable "host socket send"
        hostRecv := fun _ _ _ => unavailable "host socket receive"
        hostLocal := fun _ => unavailable "host socket local address"
        hostPeer := fun _ => unavailable "host socket peer address"
        hostShutdown := fun _ _ => unavailable "host socket shutdown"
        hostTakeError := fun _ => unavailable "host socket error query"
        setHostOption := fun _ _ _ => unavailable "host socket option set"
        getHostOption := fun _ _ => unavailable "host socket option get"
        resolve := fun _ _ => unavailable "host address resolution"
        nextAddress := fun _ => unavailable "host address iterator"
        dropIterator := fun _ => unavailable "host address iterator cleanup"
        resolutionDiagnostic := fun _ => unavailable "host resolver diagnostic"
        deadline := fun _ => unavailable "host socket deadline"
        connectingNameWarningOnce := unavailable "connecting-name diagnostic"
        edgeBackend := true
        newPoll := unavailable "mio poll creation"
        dropPoll := fun _ => unavailable "mio poll cleanup"
        registerHostSource := fun _ _ _ _ => unavailable "mio source registration"
        pollHost := fun _ _ _ => unavailable "mio poll" }
      sync := {
        ioError := unavailableIoError "linux"
        windowsTrue := unavailable "Windows synchronization result"
        windowsFalse := unavailable "Windows synchronization result"
        windowsTimeoutError := unavailable "Windows synchronization timeout" }
      clock := {
        monotonicNow := unavailable "host monotonic clock"
        systemNow := unavailable "host system clock"
        unixEpoch := ()
        checkedAddMonotonic := fun _ _ => unavailable "host monotonic clock arithmetic"
        checkedAddSystem := fun _ _ => unavailable "host system clock arithmetic"
        durationSince := fun _ _ => unavailable "host monotonic clock subtraction"
        sleep := fun _ => unavailable "host clock sleep" }
      systemDurationSince := fun _ _ => unavailable "host system clock subtraction"
      process := {
        interrupted := fun _ => false
        handleAbnormalTermination := id } }
    geometry
    alignment
    stringScanBudget := 4096
    pollBudget := 128
    fileReferenceBudget := 4096
    watcherReferenceBudget := 4096 }
  dynSymName := fun value => match value with | .dynamicSymbol name => name | _ => ""
  checkLlvmSymbolClash := fun _ => unavailable "LLVM symbol-registry check"
  math := some (Input.NativeMathHost.host _ _)
  mathError := .none
  control := Input.EvalTerminatorMachine.controlAccess
  blockingSources := Input.EvalTerminatorMachine.ioSourcesAccess }

private structure InitTrace where
  cursor : Nat := 0

-- Finite replay of an actual pinned mio::Poll::new/drop probe. No live poll
-- capability escapes isolated initialization; foreign poll/register stay unsupported.
private def rawInitHooks : Input.HostRuntime.Hooks InitTrace Poll Instant System Native Profiler := {
  createProfiler := fun _ => unavailable "profiler creation"
  newPoll := do
    let st ← get
    unless st.cursor == 0 do throw (.invalidProgram "unexpected raw poll creation replay")
    set {st with cursor := 1}
    pure ()
  dropPoll := fun _ => do
    let st ← get
    unless st.cursor == 1 do throw (.invalidProgram "unexpected raw poll drop replay")
    set {st with cursor := 2}
  hostClock := {
    monotonicNow := unavailable "host monotonic clock"
    systemNow := unavailable "host system clock"
    unixEpoch := ()
    checkedAddMonotonic := fun _ _ => unavailable "host monotonic arithmetic"
    checkedAddSystem := fun _ _ => unavailable "host system arithmetic"
    durationSince := fun _ _ => unavailable "host clock subtraction"
    sleep := fun _ => unavailable "host sleep" }
  loadNative := fun _ => unavailable "native library loading"
  dropNative := fun _ => unavailable "native library cleanup"
  dropProfiler := fun _ => unavailable "profiler cleanup" }

private def stateInfo (state : OuterState) : String := Id.run do
  let world := state.machine.user.user.payload.payload
  let stage := world.main.map fun data => match data.stage with
    | .globalConstructors .. => "globalConstructors"
    | .running => "running"
    | .exiting .. => "exiting"
  let frame := state.stack.currentFrame?.map fun frame =>
    s!"instance={reprStr frame.functionInstance}, location={reprStr frame.location}, body={reprStr frame.bodyIdentity}"
  return s!"choice_cursor={world.choices.cursor}; main_stage={stage}; active_frame={frame}"

private def preflightSnapshot (state : OuterState) : String := Id.run do
  let machine := state.machine
  let world := machine.user.user.payload.payload
  return s!"{stateInfo state}; memory_ids={machine.memory.issuedIds.size}; live={machine.memory.live.size}; dead={machine.memory.dead.size}; globals={machine.memory.globals.size}; threads={reprStr machine.threads}; choice_tape={reprStr world.choices}"

private def summarize (result : Input.EvalSourceRunFinalization.Result OuterState) : String :=
  match result with
  | .finished state code => s!"finalized_exit code={code}; {stateInfo state}"
  | .undefinedBehavior state error => s!"undefined_behavior {reprStr error}; {stateInfo state}"
  | .unsupported state error => s!"unsupported {reprStr error}; {stateInfo state}"
  | .failed state error => s!"failed {reprStr error}; {stateInfo state}"
  | .pending state cause => s!"pending {reprStr cause}; {stateInfo state}"

/-- Diagnostics retain raw MIR spans and use only exact canonical body/span
compiler hygiene queries for user-facing locations. This is separate from
allocation span hooks and does not change interpreter execution. -/
private def terminalDiagnostic (prepared : Input.EvalPreparation.Prepared)
    (result : Input.EvalSourceRunFinalization.Result OuterState) (allocationTraces : Bool := false) : Lean.Json := Id.run do
  let (kind, error, state) := match result with
    | .finished state code => ("exit", toString code, state)
    | .undefinedBehavior state error => ("ub", reprStr error, state)
    | .unsupported state error => ("unsupported", reprStr error, state)
    | .failed state error => ("failed", reprStr error, state)
    | .pending state cause => ("pending", reprStr cause, state)
  let frames := state.stack.frames.map fun frame => Id.run do
    let span? : Option SpanRef := match frame.location with
      | .unwinding span => some span
      | .mir location => do
        let block ← frame.body.basicBlocks[location.block]?
        if location.statementIndex == block.statements.size then
          some block.terminator.sourceInfo.span
        else do
          let statement ← block.statements[location.statementIndex]?
          pure statement.sourceInfo.span
    let source? := span?.bind fun span => prepared.compiler.program.bundle.spans[span.id]?
    let collapsed? : Option Input.CompilerBacktraceSource.Position := do
      let span ← span?
      let body ← prepared.compiler.program.bundle.bodies[frame.bodyIdentity.index]?
      if body.body != frame.body || body.input.instanceId != frame.functionInstance then none
      else do
        let records ← prepared.compiler.lifecycle.backtrace.bodySpans[frame.bodyIdentity.index]?
        let entries ← match records with | .ok entries => some entries | .error _ => none
        let entry ← entries.find? (·.span == span)
        pure entry.position
    return match source? with
    | none => Lean.Json.null
    | some source =>
      let raw := [
        ("raw_file", toJson (prepared.compiler.program.input.files[source.file]?)),
        ("raw_line", toJson source.start.line), ("raw_end_line", toJson source.«end».line),
        ("raw_column", toJson source.start.column),
        ("lo", toJson source.lo), ("hi", toJson source.hi),
        ("body_id", toJson frame.bodyIdentity.index), ("span_id", toJson (span?.map (·.id)))]
      match collapsed? with
      | some position => Lean.Json.mkObj (raw ++ [
          ("location_mode", toJson ("compiler_hygiene" : String)),
          ("file", toJson (prepared.compiler.program.input.files[position.filename]?)),
          ("line", toJson position.line), ("column", toJson position.column),
          ("collapsed_lo", toJson position.bytePosition.toNat)])
      | none => Lean.Json.mkObj (raw ++ [
          ("location_mode", toJson ("raw_span_no_exact_hygiene" : String)),
          ("file", toJson (prepared.compiler.program.input.files[source.file]?)),
          ("line", toJson source.start.line), ("end_line", toJson source.«end».line),
          ("column", toJson source.start.column)])
  let fields := [("kind", toJson kind), ("detail", toJson error), ("frames", .arr frames)]
  if !allocationTraces then return Lean.Json.mkObj fields
  let extras := state.machine.user.user.payload.payload.runtime.extras
  let traces := extras.allocations.filterMap fun (id, extra) => do
    let trace ← extra.backtrace
    return Lean.Json.mkObj [("allocation_id", toJson id.value.toNat),
      ("frames", .arr (trace.map fun (fnInstance, span) => Lean.Json.mkObj [
        ("instance_id", toJson fnInstance), ("span_id", toJson span.id)]))]
  return Lean.Json.mkObj (fields ++ [("allocation_backtraces", .arr traces)])

private def prepareRun (prepared : Input.EvalPreparation.Prepared)
    (initialMemory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (pageSize : UInt64) (numCpus hostPid : UInt32) (diagnosticSeed : Option UInt64)
    (profile : Lean.Options) (ui : Option UiSettings) :
    Except String ((Array ExecutionChoices.Input → Except StepError
      (Input.EvalSourceRunFinalization.Result OuterState)) ×
      (Array ExecutionChoices.Input → Except String String)) := do
  let options := (ui.map uiOptions).getD options
  let compiler := prepared.compiler
  let dummy := prepared.dummySpan
  let selectedEntry ← (Input.CompilerMain.sourceCompilerEntry compiler.main).mapError toString
  let (definition, entryType) ← match selectedEntry with
    | some entry => pure entry
    | none => do
      unless ui.isSome do throw "compiler did not select an rustc_main entry"
      pure (← Input.CompilerMiriEntry.miriStart compiler, MainEntryType.miriStart)
  let bytes ← (Input.CompilerGlobalBytes.prepare compiler.program compiler.runtime initialMemory).mapError toString
  let arrays ← compiler.initialArrays
  let targetBits := compiler.runtime.target.base.pointerWidth.bits.toNat
  let arch ← (Input.EvalArchitectureMachine.targetArch compiler.intrinsics).mapError toString
  unless compiler.program.input.producer.targetTriple == "x86_64-unknown-linux-gnu" &&
      arch == "x86_64" && targetBits == 64 do
    throw s!"fixture requires x86_64-unknown-linux-gnu; got triple={compiler.program.input.producer.targetTriple}, arch={arch}, bits={targetBits}"
  let geometry ← (Input.InitialMachine.geometry targetBits arch false none).mapError reprStr
  let sourceLeaves := sourceLeaves dummy geometry pageSize numCpus hostPid ui.isSome ((ui.map (·.alignment)).getD .Int)
  let machineConfig : Input.InitialMachine.Configuration Aff B := {
    geometry, dummySpan := dummy, provenance := (ui.map (·.provenance)).getD .default, addressMode := .managed
    addressStop := 18446744073709551615, addressReuse := ⟨0.5, if (ui.map (·.deterministicConcurrency)).getD false then 0 else 0.1⟩
    fixedScheduling := (ui.map (·.fixedScheduling)).getD false, trackOutdatedLoads := false
    weakMemory := (ui.map (·.weakMemory)).getD true
    backend := if (ui.map (·.dataRace)).getD true then .vclocks else .none
    trackedTags := if (ui.map (·.treeBorrows)).getD true then some #[] else none
    validation := options.place.validation
    alignment := (ui.map (·.alignment)).getD .Int, affinity := none, muteOutput := true, hostUsizeBits := 64 }
  let bootstrap : Input.EvalBootstrap.Configuration Os := {
    arguments := #[(ui.map (·.source)).getD "/workspace/lean-miri/scratch/main31.rs"], entry := definition, entryType
    communicate := false, forwarded := #[], environment := #[], overrides := #[] }
  let targetFacts ← compiler.externStatics.targetFacts.mapError id
  let startupFacts ← (Input.EvalStartupRuntimeConstruction.prepare compiler).mapError id
  let noCore ← startupFacts.noCore.mapError fun reason => s!"compiler no_core query: {reason}"
  let cULong ← (Input.CompilerPrimitiveFacts.cULongLayout compiler.runtime).mapError id
  let machineTarget : Input.MachineConstruction.Target := {
    os := targetFacts.os
    noCore
    cpuCount := sourceLeaves.foreignSource.host.unixConfig.numCpus
    cUlongBytes := cULong.layout.size.bytes.toNat
    endian := compiler.runtime.target.base.endian }
  let makeInitial : Array ExecutionChoices.Input → Except String (OuterState × InitTrace) := fun inputs => do
    let tape := choiceTape diagnosticSeed inputs
    let creation : EStateM.Result StepError InitTrace OuterState :=
      (Input.MachineConstruction.create rawInitHooks sourceLeaves.hostConfiguration
        machineTarget machineConfig initialMemory arrays tape).run ({} : InitTrace)
    let (initial, trace) : OuterState × InitTrace ← match creation with
      | .ok initial trace => pure (initial, trace)
      | .error error _ => throw s!"source machine construction failed: {reprStr error}"
    unless trace.cursor == 2 do throw s!"raw init trace not consumed: {trace.cursor}"
    pure (initial, trace)
  let reports : Input.EvalSourceRunFinalization.ReportEffects
      Os R Input.EvalSyncPayload.Payload H D Other Aff B Poll Instant System Native Profiler := {
    reportThreadLeak := unavailable "thread-leak diagnostic reporting"
    reportLeaks := fun _ => unavailable "allocation-leak diagnostic reporting"
    ignoreLeaksNote := if ui.isSome then pure () else unavailable "ignore-leaks diagnostic reporting"
    failureCode := -1 }
  pure (fun inputs =>
    let finalized : EStateM.Result StepError InitTrace
        (Input.EvalSourceRunFinalization.Result OuterState) :=
      Input.EvalSourceRunFinalization.runFromSourceAndFinalizeProfiled
      profile prepared prepared.image bytes options sourceLeaves () machineConfig initialMemory arrays
      (choiceTape diagnosticSeed inputs) rawInitHooks bootstrap options.limits 256 0
      [] ((ui.map (·.ignoreLeaks)).getD false) reports
      (some ⟨fun selected => by cases selected; rfl⟩) true ({} : InitTrace)
    match finalized with
    | .ok result trace => if trace.cursor == 2 then .ok result else .error (.invalidProgram "raw init trace not consumed")
    | .error error _ => .error error,
    fun inputs => do
      let (initial, trace) ← makeInitial inputs
      let before := preflightSnapshot initial
      let mismatchedConfiguration := {machineConfig with validation :=
        if machineConfig.validation == .No then .Shallow else .No}
      let result := Input.EvalSourceRunConstruction.runFromInitial
        prepared prepared.image bytes options sourceLeaves () mismatchedConfiguration bootstrap
        options.limits 256 0 [] initial
      let runResult ← result.mapError fun error => s!"runFromInitial returned outer error: {reprStr error}"
      let state ← match runResult with
        | .failed state (.invalidProgram message) =>
          unless message == "initial machine geometry/alignment/validation differs from source Core inputs" do
            throw s!"unexpected invalidProgram classification: {message}"
          pure state
        | .undefinedBehavior .. => throw "mismatched validation was classified as undefined behavior"
        | .unsupported .. => throw "mismatched validation was classified as unsupported"
        | .exited .. => throw "mismatched validation unexpectedly exited"
        | .pending .. => throw "mismatched validation unexpectedly remained pending"
        | .failed .. => throw "mismatched validation failed with the wrong error"
      unless preflightSnapshot state == before do
        throw "validation mismatch changed guest machine state before preflight rejection"
      unless trace.cursor == 2 do throw "host construction trace changed after preflight rejection"
      pure "validation_mismatch:failed_before_guest_step; state and host-init snapshots unchanged"
    )

private def initialInputs : Array ExecutionChoices.Input :=
  let allocation := (Array.replicate 512 ()).flatMap fun _ =>
    #[.boolean .addressReuse false, .index .addressSlack 0]
  let original := allocation ++ Array.replicate 8192 (.index .addressSlack 0)
  -- Prior immutable run2 established this exact requested source site.
  original.extract 0 42 ++ #[.index .globalSalt 0] ++ original.extract 42 original.size

private inductive ChoiceRepair where
  | insert (event : ExecutionChoices.Input)
  | flipBool

private def choiceRepair (message : String) : Option ChoiceRepair := Id.run do
  let indexSites : Array ExecutionChoices.IndexSite :=
    #[.atomicStale,.floatNaN,.floatMagnitude,.scheduler,.addressPool,.addressSlack,.globalSalt]
  for site in indexSites do
    if message == s!"choice input unknown: expected index at {reprStr site}" ||
        message == s!"choice input unknown: index site mismatch at {reprStr site}" then
      return some (.insert (.index site 0))
  let boolSites : Array ExecutionChoices.BoolSite := #[.weakCasSuccess,.preemption,
    .addressReuse,.addressCrossThread,.addressFreeReuse,.floatSign,.floatEqual,
    .floatFuse,.staticKnown,.signalingPow]
  for site in boolSites do
    if message == s!"choice input unknown: expected Boolean at {reprStr site}" ||
        message == s!"choice input unknown: expected probability outcome at {reprStr site}" ||
        message == s!"choice input unknown: Boolean site mismatch at {reprStr site}" ||
        message == s!"choice input unknown: probability site mismatch at {reprStr site}" then
      return some (.insert (.boolean site false))
    if message == s!"choice input unknown: Boolean outside probability support at {reprStr site}" then
      return some .flipBool
  return none

private def readJson (path : String) : IO String :=
  IO.FS.readFile (if path == "-" then "/dev/stdin" else path)

private def boundary (message : String) : IO Unit := do
  IO.println message
  (← IO.getStdout).flush

private def captureLinuxProfile : IO (UInt64 × UInt32) := do
  let page ← IO.Process.output {cmd := "getconf", args := #["PAGESIZE"]}
  if page.exitCode != 0 then throw (IO.userError s!"getconf PAGESIZE failed: {page.stderr}")
  let cpu ← IO.Process.output {cmd := "getconf", args := #["_NPROCESSORS_ONLN"]}
  if cpu.exitCode != 0 then throw (IO.userError s!"getconf _NPROCESSORS_ONLN failed: {cpu.stderr}")
  let some page := page.stdout.trimAscii.toString.toNat?
    | throw (IO.userError "getconf returned an invalid page size")
  let some cpu := cpu.stdout.trimAscii.toString.toNat?
    | throw (IO.userError "getconf returned an invalid CPU count")
  if page == 0 || cpu == 0 || page >= 2^64 || cpu >= 2^32 then
    throw (IO.userError "Linux host profile values are outside their supported range")
  pure (UInt64.ofNat page, UInt32.ofNat cpu)

def main (args : List String) : IO Unit := do
  if let ["--fingerprint", path] := args then
    let bytes ← IO.FS.readBinFile path
    let hash := bytes.foldl (fun (hash : UInt64) byte =>
      (hash ^^^ UInt64.ofNat byte.toNat) * 0x100000001b3) 0xcbf29ce484222325
    IO.println s!"upstream_fingerprint: {(Lean.Json.mkObj [
      ("byte_length", toJson bytes.size), ("fnv1a64", toJson hash.toNat)]).compress}"
    return
  let profileEnabled := args.getLast? == some "--profile"
  let args := if profileEnabled then args.dropLast else args
  let profile := if profileEnabled then
    (({} : Lean.Options).setBool `profiler true).set `profiler.threshold (0 : Nat)
    else ({} : Lean.Options)
  let some path := args.head? | throw (IO.userError "usage: NativeRunner <untouched-export.json|/dev/stdin> [--seed <u64> | --ui-source <source> --ui-flags <JSON-array>] [--profile] (gzip streamed externally)")
  let (diagnosticSeed, ui) ← match args.drop 1 with
    | [] => pure (none, none)
    | ["--seed", raw] => do
      let some value := raw.toNat? | throw (IO.userError "--seed expects an unsigned decimal u64")
      if value >= 2^64 then throw (IO.userError "--seed is outside the u64 range")
      pure (some (UInt64.ofNat value), none)
    | ["--ui-source", source, "--ui-flags", flags] =>
      let ui ← must (uiSettings source flags)
      pure (some 0, some ui)
    | _ => throw (IO.userError "usage: NativeRunner <untouched-export.json|/dev/stdin> [--seed <u64> | --ui-source <source> --ui-flags <JSON-array>] [--profile] (gzip streamed externally)")
  boundary s!"choice_mode={choiceMode diagnosticSeed}; generated_choices=unbounded; byte_length=uncapped; supplied_prefix=preserved"
  boundary "raw_host_poll: finite source initialization replay; no live poll capability"
  boundary "decode: start"
  let input ← readJson path
  let decoded ← must (Input.decodeJsonProfiled input profile)
  boundary "decode: accepted"
  boundary "lower: start"
  let program ← must (Input.lowerProgram decoded.document)
  boundary "lower: complete"
  boundary "prepare: start"
  let attempt := Input.EvalPreparation.prepareProfiled profile program
  let prepared ← must attempt.outcome
  boundary "prepare: complete"
  -- Keep the actual prepared identity tables visible at the body reported by
  -- the source105 terminal. This is diagnostic only; all lookups stay exact.
  let bodyIndex := 1814
  let bodySource := prepared.compiler.program.bundle.bodies[bodyIndex]?.map fun body =>
    s!"source_path={body.input.sourcePath}, def_path={body.input.defPath}, definition={reprStr body.input.definitionId}"
  let sourceRows := prepared.compiler.program.instances.filter (·.2 == bodyIndex)
  let callRows := (prepared.compiler.lifecycle.calls.calls.bodies.filter (·.bodyIndex == bodyIndex)).map fun row =>
    s!"fnInstance={reprStr row.fnInstance}, sourceInstanceId={row.sourceInstanceId}, bodyIndex={row.bodyIndex}"
  boundary s!"canonical_body_1814: {reprStr bodySource}; source_rows={reprStr sourceRows}; call_rows={reprStr callRows}"
  let (pageSize,hostCpus) ← captureLinuxProfile
  let numCpus := if ui.isSome then 1 else hostCpus
  let actualProfile := match ui with
    | some ui => uiProfile ui
    | none => Lean.Json.mkObj [
      ("num_cpus", toJson numCpus.toNat), ("environment_policy", toJson ("empty" : String)),
      ("argv0", toJson ("/workspace/lean-miri/scratch/main31.rs" : String)),
      ("float_nondeterminism", toJson options.floatNondeterministic),
      ("cmpxchg_weak_failure_rate_bits", toJson options.weakFailureRate.toNat),
      ("short_fd_operations", toJson false), ("choice_policy", toJson (choiceMode diagnosticSeed))]
  IO.println s!"upstream_profile: {actualProfile.compress}"
  let hostPid ← IO.Process.getPID
  boundary "run: start"
  let (execute, checkValidationMismatch) ← must
    (prepareRun prepared attempt.memory pageSize numCpus hostPid diagnosticSeed profile ui)
  let mismatch ← match checkValidationMismatch initialInputs with
    | .ok report => pure report
    | .error error => throw (IO.userError s!"validation preflight regression failed: {error}")
  boundary mismatch
  let rec plan (remaining attemptNumber : Nat) (inputs : Array ExecutionChoices.Input) : IO Unit := do
    let result ← match execute inputs with
      | .ok result => pure result
      | .error error => throw (IO.userError s!"public runner construction error: {reprStr error}")
    boundary s!"candidate={attemptNumber}: {summarize result}"
    let finish (state : OuterState) := do
      let cursor := state.machine.user.user.payload.payload.choices.cursor
      boundary s!"consumed_tape={reprStr state.machine.user.user.payload.payload.choices.inputs}"
      boundary s!"choice_events={reprStr state.machine.user.user.payload.payload.choices.events}"
      boundary s!"run: {summarize result}"
      IO.println s!"upstream_result: {(terminalDiagnostic prepared result ui.isSome).compress}"
    match result with
    | .failed state (.callback message) =>
      let some repair := choiceRepair message | return ← finish state
      match remaining with
      | 0 => boundary "run: planning_pending (explicit finite candidate bound exhausted)"
      | fuel + 1 => do
        let cursor := state.machine.user.user.payload.payload.choices.cursor
        let next ← match repair with
          | .insert event => do
            boundary s!"insert_choice cursor={cursor} event={reprStr event}"
            pure (inputs.extract 0 cursor ++ #[event] ++ inputs.extract cursor inputs.size)
          | .flipBool => do
            let some (.boolean site value) := inputs[cursor]? |
              throw (IO.userError "probability-support failure without Boolean input")
            boundary s!"flip_choice cursor={cursor} site={reprStr site} value={!value}"
            pure (inputs.set! cursor (.boolean site (!value)))
        plan fuel (attemptNumber + 1) next
    | .finished state .. | .undefinedBehavior state .. | .unsupported state .. |
      .failed state .. | .pending state .. => finish state
  plan 0 0 #[]
