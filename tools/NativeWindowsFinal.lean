import Miri.Input.EvalWindowsSourceRunFinalization
import Miri.Input.ExecutionChoicePolicy

/-! Standalone Windows source-run harness. It enters through
EvalWindowsSourceRunFinalization.runFromSourceAndFinalize. Host operations that
this fixture cannot perform remain demand-local Unsupported outcomes. -/
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter

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
private abbrev Other := Input.EvalWindowsSourceRunConstruction.Other Raw Listener TcpStream Error
private abbrev WinState := Input.EvalWindowsSourceRunConstruction.State
  Os R H D B Poll Instant System Native Profiler Raw Listener TcpStream Error
private abbrev CoreOptions := Input.EvalConfigurationCore.Options

private def unavailable {S A : Type} (name : String) : EStateM StepError S A :=
  throw (.unsupported s!"native fixture has no {name} capability")

private def fromWideAscii (units : Array UInt16) : Except StepError Os := do
  let mut bytes := ByteArray.empty
  for unit in units do
    if unit.toNat > 127 then throw (.unsupported "non-ASCII Windows OS strings in Linux host fixture")
    bytes := bytes.push (UInt8.ofNat unit.toNat)
  pure bytes

private def toWideAscii (bytes : Os) : Except StepError (Array UInt16) := do
  let mut units := #[]
  for byte in bytes.data do
    if byte.toNat > 127 then throw (.unsupported "non-ASCII Windows OS strings in Linux host fixture")
    units := units.push (UInt16.ofNat byte.toNat)
  pure units

private def windowsHostEffects (pid : UInt32) (cwd home temp : Os) :
    Input.EvalWindowsEnvironmentConstruction.HostEffects WinState Os Error := {
  communicate := false
  isolatedOp := .reject .abort
  hostPid := pure pid
  currentDirectory := pure (.ok cwd)
  setCurrentDirectory := fun _ => unavailable "host current-directory update"
  userHomeDirectory := pure (some home)
  temporaryDirectory := pure temp }

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

private def windowsOs : Input.EvalHostRuntimeConstruction.OsHostEffects Os := {
  hostWindows := false, hostUnix := true, targetWindows := true
  fromUnixBytes := id
  fromUtf8 := fun bytes => match String.fromUTF8? bytes with
    | some _ => .ok bytes
    | none => .error (.invalidProgram "invalid UTF-8 in Windows OS string")
  fromWide := fromWideAscii
  toWide := toWideAscii
  encodedBytes := id
  encodedLength := fun value => value.size
  decodeUnixBytes := fun bytes => match String.fromUTF8? bytes with
    | some _ => .ok bytes
    | none => .error (.invalidProgram "invalid UTF-8 in host path")
  empty := ByteArray.empty
  concat := fun left right => left ++ right
  ascii := fun text => text.toUTF8
  isEmpty := fun value => value.isEmpty
  containsEquals := fun value => value.data.contains 61 }

private def unavailableIoError (os : String) : IoError.Hooks S Unit := {
  family := .windows, os, hostUnix := false
  hostErrno := fun _ => unavailable "host errno translation"
  libc := fun _ => unavailable "compiler libc errno conversion"
  windows := fun _ => unavailable "Windows error conversion"
  scalarI32 := fun _ => unavailable "host error scalar conversion"
  scalarU32 := fun _ => unavailable "host error scalar conversion"
  hostFromRaw := fun _ => unavailable "raw host error conversion"
  hostFromKind := fun _ => unavailable "host error-kind conversion"
  getLastErrorPlace := unavailable "sync errno lookup"
  setLastErrorPlace := fun _ => unavailable "sync errno update"
  allocateU32Machine := unavailable "sync errno allocation"
  writeScalar := fun _ _ => unavailable "sync errno memory write"
  readScalar := fun _ => unavailable "sync errno memory read"
  writeInt := fun _ _ => unavailable "sync errno memory write" }

private def sourceLeaves (dummy : SpanRef) (geometry : Input.InitialMachine.Geometry)
    (pageSize : UInt64) (numCpus hostPid : UInt32) : Input.EvalConfigurationCore.SourceLeaves
    Os R Payload H D Aff B Poll Instant System Native Profiler Raw Listener TcpStream Error
    Unit Unit ByteArray Miri.MIR.Place Unit Instant CallInstance Unit := {
  hostConfiguration := {
    communicate := false, muteOutput := true, hostUsizeBits := 64
    profileOutput := none, nativeLibraries := #[]
    hostTriple := "x86_64-unknown-linux-gnu", targetTriple := "x86_64-pc-windows-gnu"
    nativeSupported := false
    control := ⟨0, 0x3f847ae147ae147b, true⟩ }
  nativeHost := none
  sync := Input.EvalSyncObjectAccess.onAccess
  storage := fun size _ => some (Array.replicate size.bytes.toNat 0)
  spans := ⟨dummy, false⟩
  foreignSource := {
    shortFdOperations := false
    varArgsBudget := 256
    host := {
      hostOverflowChecks := true
      os := windowsOs
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
        hostFromKind := fun _ => unavailable "host error-kind conversion" }
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
        ioError := unavailableIoError "windows"
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
    alignment := .Int
    stringScanBudget := 4096
    pollBudget := 128
    fileReferenceBudget := 4096
    watcherReferenceBudget := 4096 }
  dynSymName := fun value => match value with | .dynamicSymbol name => name | _ => ""
  checkLlvmSymbolClash := fun _ => unavailable "LLVM symbol-registry check"
  math := none
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

private def stateInfo (state : WinState) : String := Id.run do
  let world := state.machine.user.user.payload.payload
  let stage := world.main.map fun data => match data.stage with
    | .globalConstructors .. => "globalConstructors"
    | .running => "running"
    | .exiting .. => "exiting"
  let frame := state.stack.currentFrame?.map fun frame =>
    s!"instance={reprStr frame.functionInstance}, location={reprStr frame.location}, body={reprStr frame.bodyIdentity}"
  return s!"choice_cursor={world.choices.cursor}; main_stage={stage}; active_frame={frame}"

private def summarize (result : Input.EvalSourceRunFinalization.Result WinState) : String :=
  match result with
  | .finished state code => s!"finalized_exit code={code}; {stateInfo state}"
  | .undefinedBehavior state error => s!"undefined_behavior {reprStr error}; {stateInfo state}"
  | .unsupported state error => s!"unsupported {reprStr error}; {stateInfo state}"
  | .failed state error => s!"failed {reprStr error}; {stateInfo state}"
  | .pending state cause => s!"pending {reprStr cause}; {stateInfo state}"

private def prepareRun (prepared : Input.EvalPreparation.Prepared)
    (initialMemory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (pageSize : UInt64) (numCpus : UInt32)
    (hostData : UInt32 × Os × Os × Os) :
    Except String (Array ExecutionChoices.Input → Except StepError
    (Input.EvalSourceRunFinalization.Result WinState)) := do
  let compiler := prepared.compiler
  let dummy := prepared.dummySpan
  let selectedEntry ← (Input.CompilerMain.sourceCompilerEntry compiler.main).mapError toString
  let some (definition, .rustcMain sigpipe) := selectedEntry
    | throw "compiler did not select an rustc_main entry"
  let bytes ← (Input.CompilerGlobalBytes.prepare compiler.program compiler.runtime initialMemory).mapError toString
  let arrays ← compiler.initialArrays
  let (hostPid,cwd,home,temp) := hostData
  let targetBits := compiler.runtime.target.base.pointerWidth.bits.toNat
  let arch ← (Input.EvalArchitectureMachine.targetArch compiler.intrinsics).mapError toString
  unless compiler.program.input.producer.targetTriple == "x86_64-pc-windows-gnu" &&
      arch == "x86_64" && targetBits == 64 do
    throw s!"fixture requires x86_64-pc-windows-gnu; got triple={compiler.program.input.producer.targetTriple}, arch={arch}, bits={targetBits}"
  let geometry ← (Input.InitialMachine.geometry targetBits arch false none).mapError reprStr
  let sourceLeaves := sourceLeaves dummy geometry pageSize numCpus hostPid
  let machineConfig : Input.InitialMachine.Configuration Aff B := {
    geometry, dummySpan := dummy, provenance := .default, addressMode := .managed
    addressStop := 18446744073709551615, addressReuse := ⟨0.5, 0.1⟩
    fixedScheduling := false, trackOutdatedLoads := false, weakMemory := true
    backend := .vclocks, trackedTags := some #[], validation := .Shallow
    alignment := .Int, affinity := none, muteOutput := true, hostUsizeBits := 64 }
  let bootstrap : Input.EvalBootstrap.Configuration Os := {
    arguments := #["C:\\lean-miri\\scratch\\windows_normal_main.exe"], entry := definition, entryType := .rustcMain sigpipe
    communicate := false, forwarded := #[], environment := #[], overrides := #[] }
  let reports : Input.EvalSourceRunFinalization.ReportEffects
      Os R Input.EvalSyncPayload.Payload H D Other Aff B Poll Instant System Native Profiler := {
    reportThreadLeak := unavailable "thread-leak diagnostic reporting"
    reportLeaks := fun _ => unavailable "allocation-leak diagnostic reporting"
    ignoreLeaksNote := unavailable "ignore-leaks diagnostic reporting"
    failureCode := -1 }
  let windowsHost := windowsHostEffects hostPid cwd home temp
  let pathToOs := fun path : ByteArray => windowsOs.fromUnixBytes path
  pure fun inputs =>
    match Input.EvalWindowsSourceRunFinalization.runFromSourceAndFinalize
      prepared bytes options sourceLeaves windowsHost pathToOs () machineConfig initialMemory arrays
      (Input.ExecutionChoicePolicy.diagnosticTape 4096 4096 inputs) rawInitHooks bootstrap options.limits 256 100000
      (List.replicate 100000 ()) false reports |>.run {} with
    | .ok result trace =>
      if trace.cursor == 2 then .ok result
      else .error (.invalidProgram "raw init trace not consumed")
    | .error error _ => .error error

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

private def captureHostProfile : IO (UInt64 × UInt32) := do
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

private def captureHostDirectories : IO (Os × Os × Os) := do
  let cwd ← IO.currentDir
  let home ← IO.getEnv "HOME"
  pure (cwd.toString.toUTF8, (home.getD "/").toUTF8, "/tmp".toUTF8)

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "usage: NativeRunner <untouched-export.json|/dev/stdin> (gzip streamed externally)")
  boundary "raw_host_poll: finite source initialization replay; no live poll capability"
  boundary "decode: start"
  let input ← readJson path
  let decoded ← must (Input.decodeJson input)
  unless decoded.executionInput.isSome && decoded.blockingObligations.isEmpty do
    let sample := decoded.blockingObligations.toList.take 40
    throw (IO.userError s!"strict readiness gate failed: {decoded.blockingObligations.size} blocking obligations; sample={reprStr sample}")
  boundary s!"decode: ready obligations={decoded.blockingObligations.size}"
  boundary "lower: start"
  let program ← must (Input.lowerProgram decoded.document)
  boundary "lower: complete"
  boundary "prepare: start"
  let attempt := Input.EvalPreparation.prepare program
  let prepared ← must attempt.outcome
  boundary "prepare: complete"
  let (pageSize,numCpus) ← captureHostProfile
  let hostPid ← IO.Process.getPID
  let (cwd,home,temp) ← captureHostDirectories
  boundary "run: start"
  let execute ← must (prepareRun prepared attempt.memory pageSize numCpus (hostPid,cwd,home,temp))
  let rec plan (remaining attemptNumber : Nat) (inputs : Array ExecutionChoices.Input) : IO Unit := do
    let result ← match execute inputs with
      | .ok result => pure result
      | .error error => throw (IO.userError s!"public runner construction error: {reprStr error}")
    boundary s!"candidate={attemptNumber}: {summarize result}"
    let finish (state : WinState) := do
      boundary s!"consumed_tape={reprStr state.machine.user.user.payload.payload.choices.inputs}"
      boundary s!"choice_events={reprStr state.machine.user.user.payload.payload.choices.events}"
      boundary s!"run: {summarize result}"
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
  plan 256 0 (initialInputs)
