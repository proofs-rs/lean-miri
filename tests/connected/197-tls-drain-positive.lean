import Miri.Input.EvalSourceRunFinalization
import Miri.Input.ExecutionChoicePolicy
import Miri.Input.NativeMathHost

/-! Verification-only pthread TLS destructor-drain harness for retained `miri_start`
fixtures. It constructs the canonical source Core and callback package, then
connects the source Unix/Pthread foreign hooks to the local scheduler with
fixedScheduling disabled. Host operations outside this execution remain
demand-local Unsupported outcomes. -/
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
private abbrev Other := Input.EvalUnixSourceConstruction.Other Raw Listener TcpStream Error
private abbrev Host := Input.EvalConfigurationCore.SourceHost Poll Instant System H D Raw Listener TcpStream Error Native Profiler
private abbrev CoreUser := Input.EvalCoreMachine.User Os R Payload H D Other Aff B Host
private abbrev OuterState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Outer
    (Input.EvalWorld.World Os R Payload H D Other Aff B Host))
private abbrev CoreOptions := Input.EvalConfigurationCore.Options

private def unavailable {S A : Type} (name : String) : EStateM StepError S A :=
  throw (.unsupported s!"native fixture has no {name} capability")

private def must {A : Type} (value : Except String A) : Except String A :=
  match value with
  | .ok result => pure result
  | .error reason => throw reason

private def options : CoreOptions := {
  place := {debugAssertions := false, dynamicFuel := 256, validation := .Shallow}
  limits := {callDispatch := 128, casts := 128, retag := 128, validation := 128}
  compatibilityBudget := 128, varArgsBudget := 128, callbackCapacity := 128
  floatNondeterministic := false, weakFailureRate := 0, crossCrateInlineAlways := false
  userRelevantCrates := #[], ignoreOptionalOverflowChecks := false, panicUnwinds := false
  retag := {implicitWrites := false, preciseInteriorMut := true} }

private def choiceTape (seed : Option UInt64) (inputs : Array ExecutionChoices.Input) :=
  match seed with
  | none => Input.ExecutionChoicePolicy.diagnosticTape 65536 4096 inputs
  | some value => Input.ExecutionChoicePolicy.seededDiagnosticTape 65536 4096 value inputs

private def choiceMode (seed : Option UInt64) : String :=
  match seed with
  | none => "bounded-diagnostic-zero"
  | some value => s!"bounded-seeded-diagnostic seed={value.toNat} algorithm=SplitMix64-v1"

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

private def unavailableIoError (os : String) : IoError.Hooks S Unit := {
  family := .unix, os, hostUnix := true
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
    shortFdOperations := false
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
    alignment := .Int
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

private def stateInfo (state : OuterState) : String := Id.run do
  let world := state.machine.user.user.payload.payload
  let frame := state.stack.currentFrame?.map fun frame =>
    s!"instance={reprStr frame.functionInstance}, location={reprStr frame.location}"
  return s!"threads={state.machine.threads.threads.length}; choice_cursor={world.choices.cursor}; active_frame={frame}"

private def runTlsDrainPure (contents : String) (pageSize : UInt64)
    (numCpus hostPid : UInt32) : Except String String := do
  let decoded ← must (Input.decodeRuntimeJson contents)
  unless decoded.executionInput.isSome && decoded.blockingObligations.isEmpty do
    throw s!"strict readiness gate failed: obligations={decoded.blockingObligations.size}; sample={reprStr (decoded.blockingObligations.toList.take 30)}"
  let program ← must (Input.lowerCoreProgram decoded.document)
  let attempt := Input.EvalPreparation.prepare program
  let prepared ← must attempt.outcome
  let compiler := prepared.compiler
  let image := prepared.image
  let memory := attempt.memory
  let bytes ← must (Input.CompilerGlobalBytes.prepare compiler.program compiler.runtime memory
    (some compiler.sourceEquality))
  let targetBits := compiler.runtime.target.base.pointerWidth.bits.toNat
  let arch ← must (Input.EvalArchitectureMachine.targetArch compiler.intrinsics)
  unless compiler.program.input.producer.targetTriple == "x86_64-unknown-linux-gnu" &&
      arch == "x86_64" && targetBits == 64 do
    throw s!"TLS drain fixture requires x86_64-unknown-linux-gnu; triple={compiler.program.input.producer.targetTriple}, arch={arch}, bits={targetBits}"
  let geometry ← match Input.InitialMachine.geometry targetBits arch false none with
    | .ok value => pure value
    | .error reason => throw s!"target geometry failed: {reprStr reason}"
  let sourceLeaves := sourceLeaves prepared.dummySpan geometry pageSize numCpus hostPid
  let targetFacts ← match compiler.externStatics.targetFacts with
    | .ok value => pure value
    | .error reason => throw s!"target facts unavailable: {reason}"
  let startupFacts ← must (Input.EvalStartupRuntimeConstruction.prepare compiler)
  let noCore ← match startupFacts.noCore with
    | .ok value => pure value
    | .error reason => throw s!"compiler no_core query unavailable: {reason}"
  let cULong ← must (Input.CompilerPrimitiveFacts.cULongLayout compiler.runtime)
  let machineTarget : Input.MachineConstruction.Target := {
    os := targetFacts.os
    noCore
    cpuCount := numCpus
    cUlongBytes := cULong.layout.size.bytes.toNat
    endian := compiler.runtime.target.base.endian }
  let options : Input.EvalConfigurationCore.Options := {
    place := {debugAssertions := false, dynamicFuel := 256, validation := .Shallow}
    limits := {callDispatch := 128, casts := 128, retag := 128, validation := 128}
    compatibilityBudget := 128, varArgsBudget := 256, callbackCapacity := 128
    floatNondeterministic := false, weakFailureRate := 0, crossCrateInlineAlways := false
    userRelevantCrates := #[], ignoreOptionalOverflowChecks := false, panicUnwinds := false
    retag := {implicitWrites := false, preciseInteriorMut := true} }
  let machineConfig : Input.InitialMachine.Configuration Aff B := {
    geometry, dummySpan := prepared.dummySpan, provenance := .default, addressMode := .managed
    addressStop := 18446744073709551615, addressReuse := ⟨0.5, 0.1⟩
    fixedScheduling := false, trackOutdatedLoads := false, weakMemory := true
    backend := .vclocks, trackedTags := some #[], validation := .Shallow
    alignment := .Int, affinity := none, muteOutput := true, hostUsizeBits := 64 }
  let arrays ← must compiler.initialArrays
  let tape := choiceTape none #[]
  let creation : EStateM.Result StepError InitTrace OuterState :=
    (Input.MachineConstruction.create rawInitHooks sourceLeaves.hostConfiguration
      machineTarget machineConfig memory arrays tape).run ({} : InitTrace)
  let (initial, trace) ← match creation with
    | .ok state trace => pure (state, trace)
    | .error error _ => throw s!"canonical source machine construction failed: {reprStr error}"
  unless trace.cursor == 2 do throw s!"host initialization replay incomplete: {trace.cursor}"
  let some root := (compiler.program.rootDefinitionId 0).toOption
    | throw "prepared source export does not identify root miri_start"
  let bootConfig : Input.EvalBootstrap.Configuration Os := {
    arguments := #[], entry := root, entryType := .miriStart
    communicate := false, forwarded := #[], environment := #[], overrides := #[] }
  match Input.EvalConfigurationCore.makeFromSourcePackage compiler image bytes options sourceLeaves ()
      options.callbackCapacity with
  | .error error => throw s!"canonical source Core construction failed: {reprStr error}"
  | .ok package => do
    let execution := package.execution
    let context := package.context
    let some buildAssembly := context.sourceAssembly
      | throw "canonical source Core lacks its source assembly"
    let (afterAssembly, assemblyResult) := MachineHooks.run
      (ExecutionStateTransport.action (buildAssembly ())) initial
    let assembly ← match assemblyResult with
      | .ok assembly => pure assembly
      | .error error => throw s!"canonical source assembly failed: {reprStr error}"
    let some envMemory := assembly.memory
      | throw "canonical source assembly lacks startup environment memory"
    let some _ := assembly.environment
      | throw "canonical source assembly lacks startup environment hooks"
    let limits := options.limits
    match Input.EvalSourceRunConstruction.sourceMainFromExecution
        prepared execution limits () sourceLeaves.spans envMemory afterAssembly with
    | .error error => throw s!"source main construction failed: {reprStr error}"
    | .ok main => do
      let arguments ← must (Input.EvalStartupRuntimeConstruction.argumentsFromExecution
        compiler execution startupFacts)
      let family : ForeignItems.Family :=
        if targetFacts.os == "windows" || targetFacts.families.contains "windows" then .windows
        else if targetFacts.families.contains "unix" then .unix else .other
      let environment := Input.EvalStartupAssembly.environmentFromSource sourceLeaves.foreignSource.host.os
        sourceLeaves.foreignSource.host.environment family envMemory
      let target := Input.EvalHostRuntimeConstruction.ExternStaticTarget.fromCompiler targetFacts
      let u8Facts ← must (Input.CompilerPrimitiveFacts.primitiveLayout compiler.runtime "u8")
      let usizeFacts ← must (Input.CompilerPrimitiveFacts.primitiveLayout compiler.runtime "usize")
      let u8Layout : LocalLayout := ⟨u8Facts.ty, u8Facts.layout⟩
      let usizeLayout : LocalLayout := ⟨usizeFacts.ty, usizeFacts.layout⟩
      let dynamicValue := fun name => SourceOther.Value.dynamicSymbol name
      let externStatics := Input.EvalStartupAssembly.externStaticsFromSource target
        envMemory execution.functions dynamicValue u8Layout usizeLayout
      let bootstrap := Input.EvalSourceRunConstruction.assembleBootstrapHooks
        (Os := Os) (R := R) (P := Payload) (H := H) (D := D)
        (O := Other) (Aff := Aff) (B := B)
        (Host := Host) (C := Unit) (ClockHost := Instant)
        (arguments := ⟨arguments⟩) main environment externStatics compiler image
        (Input.EvalStartupAssembly.vtableRuntimeFromExecution prepared execution) bootConfig
      let bootConfig := bootstrap.1
      let hooks := bootstrap.2
      let (afterInit, initResult) := MachineHooks.run
        (Input.EvalBootstrap.createContextWithBytes hooks bootConfig ()) afterAssembly
      let _bytesAttached ← match initResult with
        | .ok value => pure value
        | .error error => throw s!"canonical MiriStart initialization failed: {reprStr error}"
      match package.callbackBuilder assembly execution hooks.main afterInit with
      | .error (error, state) => throw s!"canonical callback construction failed: {reprStr error}; {stateInfo state}"
      | .ok (callbackProduct, afterCallbacks) => do
        let bindPackage := fun selectedExecution => do
          let rebound := package.rebindCallbacks callbackProduct selectedExecution
          let some foreign := rebound.calls.dispatch.foreign
            | throw (.unsupported "selected source Core lacks callback-rebound foreign hooks")
          let connectedForeign := do
            let foreignHooks ← foreign
            match Input.EvalMiriConnectedSourceConstruction.bind compiler image
                {options with panicUnwinds := package.panicUnwinds} sourceLeaves context
                callbackProduct.main.termination.tls.thread foreignHooks with
              | .ok connected => pure connected
              | .error error => throw error
          let dispatch := {rebound.calls.dispatch with foreign := some connectedForeign}
          let calls := {rebound.calls with dispatch}
          pure {rebound with calls}
        let configs := fun _ => bindPackage execution
        let callbacks := callbackProduct.hooks
        let choiceAccess := Input.EvalSourceRunConstruction.sourceChoiceAccess
          (Os := Os) (R := R) (H := H) (D := D)
          (O := Other) (Aff := Aff) (B := B)
          (Poll := Poll) (Instant := Instant) (System := System)
          (Native := Native) (Profiler := Profiler)
          (Raw := Raw) (Listener := Listener) (TcpStream := TcpStream) (Error := Error)
        let clock := Input.EvalSourceRunConstruction.sourceClockToOuter
          sourceLeaves.foreignSource.host.clock
        let durationSince := Input.EvalSourceRunConstruction.sourceDurationSinceToOuter
          sourceLeaves.foreignSource.host.systemDurationSince
        let hostProcess := sourceLeaves.foreignSource.host.process
        let process : Input.EvalRunConstruction.ProcessEffects OuterState := {
          interrupted := fun state => hostProcess.interrupted (ExecutionStateTransport.inward state)
          handleAbnormalTermination := fun state => ExecutionStateTransport.outward
            (hostProcess.handleAbnormalTermination (ExecutionStateTransport.inward state)) }
        let loop := Input.EvalRunConstruction.hooksFromSource
          sourceLeaves.hostConfiguration callbacks hooks.main configs limits choiceAccess clock durationSince process
        let result := Input.EvalRunConstruction.runUntilTerminal loop 100000
          (List.replicate 100000 ()) afterCallbacks
        match result with
        | .undefinedBehavior state error =>
          throw s!"TLS drain fixture produced unexpected undefined behavior: {reprStr error}; {stateInfo state}"
        | .unsupported state error =>
          throw s!"tls_drain_result=unsupported; error={reprStr error}; {stateInfo state}"
        | .failed state error =>
          throw s!"tls_drain_result=failed; error={reprStr error}; {stateInfo state}"
        | .pending state cause =>
          throw s!"tls_drain_result=pending; cause={reprStr cause}; {stateInfo state}"
        | .exited state code leakCheck => do
          unless code == 0 do
            throw s!"TLS drain fixture returned nonzero source status {code}; leak_check={leakCheck}; {stateInfo state}"
          unless leakCheck do
            throw s!"TLS drain fixture exited with leak checking disabled or incomplete; {stateInfo state}"
          unless state.machine.threads.threads.length == 2 do
            throw s!"TLS drain fixture exited without the expected two thread records: {stateInfo state}"
          pure s!"canonical_source_route=makeFromSourcePackage+callbackBuilder+MiriConnected+hooksFromSource\nsource_entry=miri_start; scheduler=fixedScheduling_false; foreign=canonical Unix/Pthread\noutcome=exit_zero; leak_check={leakCheck}; {stateInfo state}"

def main (args : List String) : IO Unit := do
  let some input := args.head? | throw (IO.userError "usage: TlsDrain <untouched-export.json>")
  let contents ← IO.FS.readFile input
  let (pageSize, numCpus) ← captureLinuxProfile
  let hostPid ← IO.Process.getPID
  let report ← match runTlsDrainPure contents pageSize numCpus hostPid with
    | .ok report => pure report
    | .error error => throw (IO.userError error)
  IO.println report
