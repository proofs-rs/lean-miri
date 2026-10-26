import MiriTests.Connected.Proofs.ChoiceHistory206
import Miri.Input.EvalSourceRunFinalization
import Miri.Input.ExecutionChoicePolicy
import Miri.Input.NativeMathHost
import MiriTests.Connected.Proofs.ExactStateCodec207
import MiriTests.Connected.Proofs.FastStateDecEq225

/-! Verification-only SeqCst store-buffering harness for retained `miri_start`
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
private abbrev OuterState := ExactStateCodec207.OuterState
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

private def raceStateInfo (state : OuterState) : String := Id.run do
  let world := state.machine.user.user.payload.payload
  let frame := state.stack.currentFrame?.map fun frame =>
    s!"instance={reprStr frame.functionInstance}, location={reprStr frame.location}"
  return s!"threads={state.machine.threads.threads.length}; choice_cursor={world.choices.cursor}; active_frame={frame}"

/-- Equality-preserving coarse bucket refinement. These fields are only a hash
hint: a matching key always falls through to full `OuterState` equality. In
particular, omitting any other state field can only create collisions, never
permit an unsound merge. -/
private def mainStageBucketInfo (state : OuterState) : String := Id.run do
  let world := state.machine.user.user.payload.payload
  match world.main with
  | none => return "main=none"
  | some main =>
    let stage := match main.stage with
      | .globalConstructors .. => "globalConstructors"
      | .running => "running"
      | .exiting .tls code => s!"exit-tls:{code.toInt}"
      | .exiting (.yield remaining) code => s!"exit-yield:{remaining.toNat}:{code.toInt}"
      | .exiting .done code => s!"exit-done:{code.toInt}"
      | .exiting .unreachable code => s!"exit-unreachable:{code.toInt}"
    return s!"main-token={main.token};stage={stage}"

private def stateBucketKey (state : OuterState) (inactivePcs : List (String × Option (String × String))) : UInt64 := Id.run do
  let world := state.machine.user.user.payload.payload
  let memory := state.machine.memory
  let host := world.host
  let control := host.control
  -- MainData.stage is included because ordinary Miri startup-to-exit passes
  -- through 256 genuine MainMachine `.yield remaining` states. This remains
  -- only a bucket key: full OuterState Eq is still the only merge criterion.
  return hash (raceStateInfo state, inactivePcs,
    reprStr state.machine.threads, reprStr state.machine.dataRace,
    memory.nextAllocId, memory.live.size, memory.dead.size,
    control.basicBlockCount, control.sinceGc, reprStr host.clock,
    mainStageBucketInfo state)

private structure ReplayNode where
  state : OuterState
  inputs : Array ExecutionChoices.Input
  path : String

private structure GraphReport where
  processed : Nat := 0
  uniqueStates : Nat := 0
  mergedStates : Nat := 0
  stateEqChecks : Nat := 0
  executedSteps : Nat := 0
  branchPoints : Nat := 0
  generatedNodes : Nat := 0
  nodeLines : Array String := #[]
  branchLines : Array String := #[]
  terminalLines : Array String := #[]
  unresolvedLines : Array String := #[]
  openFrontierCount : Nat := 0
  openFrontier : Array String := #[]

private def requestedInputs (event : ExecutionChoices.Event) : Array ExecutionChoices.Input := Id.run do
  match event.request with
  | .index .scheduler count =>
      return (Array.range count).map fun value => .index .scheduler value
  | .index .atomicStale count =>
      return (Array.range count).map fun value => .index .atomicStale value
  | .boolean .preemption =>
      return #[.boolean .preemption false, .boolean .preemption true]
  | .bernoulli .preemption rateBits =>
      let permits (value : Bool) :=
        match TerminatorMachine.permitsPreemption rateBits value with
        | .ok allowed => allowed
        | .error _ => false
      return (#[false, true].filter permits).map fun value => .boolean .preemption value
  | _ => return #[]

private def runStatus
    (result : Input.EvalRunConstruction.RunResult OuterState) : String :=
  match result with
  | .pending _ cause => s!"pending:{reprStr cause}"
  | .exited _ code leak => s!"exited:code={code};leak={leak}"
  | .undefinedBehavior _ error => s!"undefined_behavior:{reprStr error}"
  | .unsupported _ error => s!"unsupported:{reprStr error}"
  | .failed _ error => s!"failed:{reprStr error}"

private def stateFromRun
    (result : Input.EvalRunConstruction.RunResult OuterState) : OuterState :=
  match result with
  | .pending state _ | .exited state _ _ | .undefinedBehavior state _
  | .unsupported state _ | .failed state _ => state

private def isOneIterationPrefix
    (result : Input.EvalRunConstruction.RunResult OuterState) : Bool :=
  match result with
  | .pending _ (.outerChoicesExhausted 1) => true
  | _ => false

private def exploreConnected [DecidableEq OuterState] {Callback : Type}
    (loop : RunLoopHooks OuterState Unit Callback)
    (choiceAccess : ExecutionChoices.Access OuterState)
    (initial : OuterState) (nodeBudget : Nat) : GraphReport := Id.run do
  let initialTape := ChoiceHistory206.eraseConsumedHistory (choiceAccess.get initial)
  let initial := choiceAccess.put initial {initialTape with policy := .strict}
  let mut queue : Array ReplayNode := #[⟨initial, #[], "root"⟩]
  let mut visited : Std.HashMap UInt64 (Array (Nat × OuterState)) := {}
  let mut report : GraphReport := {}
  while !queue.isEmpty && report.processed < nodeBudget do
    let some node := queue.back? | break
    queue := queue.pop
    let nodeNumber := report.processed
    report := {report with processed := report.processed + 1}
    if report.processed % 100 == 0 then
      dbg_trace s!"PROGRESS processed={report.processed};queue={queue.size};unique={report.uniqueStates};merges={report.mergedStates};state_eq_checks={report.stateEqChecks}"
    -- Hashing selects a bucket only. Every positive merge uses actual Eq.
    if node.inputs.isEmpty then
      let inactivePcs := node.state.machine.user.registry.inactive.map fun entry =>
        (reprStr entry.thread, entry.stack.currentFrame?.map fun frame =>
          (reprStr frame.functionInstance, reprStr frame.location))
      let key := stateBucketKey node.state inactivePcs.toList
      let bucket := visited.getD key #[]
      let mut exactPrevious : Option (Nat × OuterState) := none
      for previous in bucket do
        report := {report with stateEqChecks := report.stateEqChecks + 1}
        if decide (previous.2 = node.state) then
          exactPrevious := some previous
          break
      if let some previous := exactPrevious then
        let line := s!"node={nodeNumber};path={node.path};status=merged_exact_normalized_state;merged_into={previous.1}"
        report := {report with mergedStates := report.mergedStates + 1, nodeLines := report.nodeLines.push line}
        continue
      visited := visited.insert key (bucket.push (nodeNumber, node.state))
      report := {report with uniqueStates := report.uniqueStates + 1}
    let preTape := choiceAccess.get node.state
    let used := preTape.inputs.extract 0 preTape.cursor
    let replayTape := {preTape with
      inputs := used ++ node.inputs
      policy := .boundedDiagnostic 65536 4096}
    let replayState := choiceAccess.put node.state replayTape
    -- Diagnostic execution proposes a complete finite input sequence only.
    -- The graph edge itself is a separate strict execution from the saved state.
    let probe := Input.EvalRunConstruction.runUntilTerminal loop 1 [()] replayState
    let probeTape := choiceAccess.get (stateFromRun probe)
    let proposedEvents := probeTape.events.extract preTape.events.size probeTape.events.size
    let strictTape := {preTape with
      inputs := used ++ proposedEvents.map (·.input)
      policy := .strict}
    let strictState := choiceAccess.put node.state strictTape
    let result := Input.EvalRunConstruction.runUntilTerminal loop 1 [()] strictState
    let afterState := stateFromRun result
    let afterTape := choiceAccess.get afterState
    let newEvents := afterTape.events.extract preTape.events.size afterTape.events.size
    let status := runStatus result
    report := {report with executedSteps := report.executedSteps + 1}
    let eventText := reprStr newEvents.toList
    let nodeLine := s!"node={nodeNumber};path={node.path};prefix={reprStr node.inputs};status={status};events={eventText}"
    report := {report with nodeLines := report.nodeLines.push nodeLine}

    -- A mismatch is an unresolved harness obligation, never an accepted edge.
    if decide (newEvents ≠ proposedEvents) || afterTape.generatedChoices != preTape.generatedChoices then
      let mismatch := s!"node={nodeNumber};strict_replay_mismatch;status={status};probe_status={runStatus probe}"
      report := {report with unresolvedLines := report.unresolvedLines.push mismatch}
      continue
    let mut foundBranch : Option (Nat × ExecutionChoices.Event × Array ExecutionChoices.Input) := none
    for index in [:newEvents.size] do
      if index >= node.inputs.size && foundBranch.isNone then
        if let some event := newEvents[index]? then
          let support := requestedInputs event
          if support.size > 1 then foundBranch := some (index, event, support)
    if let some (index, event, support) := foundBranch then
      report := {report with
        branchPoints := report.branchPoints + 1
        generatedNodes := report.generatedNodes + support.size}
      let branchLine := s!"branch_node={nodeNumber};event_index={index};request={reprStr event.request};actual={reprStr event.input};complete_support={reprStr support}"
      report := {report with branchLines := report.branchLines.push branchLine}
      let forcedBefore := (newEvents.extract 0 index).map (·.input)
      for alternative in support do
        let inputs := forcedBefore.push alternative
        let altText := reprStr alternative
        let path := s!"parent={nodeNumber}/event={index}:{altText}"
        queue := queue.push ⟨node.state, inputs, path⟩
    else if isOneIterationPrefix result then
      let consumedTape := choiceAccess.get afterState
      if consumedTape.cursor != consumedTape.inputs.size then
        let line := s!"node={nodeNumber};unexpected_unconsumed_step_input_cursor={consumedTape.cursor};size={consumedTape.inputs.size}"
        report := {report with unresolvedLines := report.unresolvedLines.push line}
        continue
      let normalized := ChoiceHistory206.eraseConsumedHistory consumedTape
      let nextState := choiceAccess.put afterState normalized
      queue := queue.push ⟨nextState, #[], s!"parent={nodeNumber}/continuation"⟩
    else if status.startsWith "exited:" then
      let terminalLine := s!"node={nodeNumber};path={node.path};status={status};events={eventText}"
      report := {report with terminalLines := report.terminalLines.push terminalLine}
    else
      let unresolvedLine := s!"node={nodeNumber};path={node.path};status={status};events={eventText}"
      report := {report with unresolvedLines := report.unresolvedLines.push unresolvedLine}

  if !queue.isEmpty then
    report := {report with
      openFrontierCount := queue.size
      openFrontier := queue.toList.take 20 |>.toArray |>.map fun node =>
      (s!"path={node.path};prefix={reprStr node.inputs};{raceStateInfo node.state}")}
  return report

private def renderGraphReport (report : GraphReport) : String := Id.run do
  let mut lines := #[
    "graph215:classification=prototype_only;no_safe_acceptance_claim",
    s!"processed_nodes={report.processed};branch_points={report.branchPoints};generated_replay_nodes={report.generatedNodes};open_frontier_count={report.openFrontierCount};open_frontier_sample_count={report.openFrontier.size}",
    s!"state_identity=exact_Eq_after_strict_history_erasure;unique_states={report.uniqueStates};merged_states={report.mergedStates};state_eq_checks={report.stateEqChecks};executed_steps={report.executedSteps};traversal=depth-first",
    "edge_policy=strict finite supplied inputs; diagnostic probe proposes inputs only; nonbranched sites fixed to diagnostic defaults; startup/address/host parameters fixed",
    "branched_sites=ExecutionChoices.IndexSite.scheduler, IndexSite.atomicStale, BoolSite.preemption (both Bernoulli-supported outcomes)",
    "all UB, Unsupported, failed, resource-exhaustion, choice-tape-exhaustion, and pending outcomes remain unresolved and are not classified safe"
  ]
  if report.openFrontier.isEmpty then lines := lines.push "frontier=empty"
  for line in report.nodeLines do lines := lines.push line
  for line in report.branchLines do lines := lines.push line
  for line in report.terminalLines do lines := lines.push s!"terminal:{line}"
  for line in report.unresolvedLines do lines := lines.push s!"unresolved:{line}"
  for line in report.openFrontier do lines := lines.push s!"frontier:{line}"
  return String.intercalate "\n" lines.toList

private def runScLitmusPure [DecidableEq OuterState] (contents : String) (nodeBudget : Nat) (pageSize : UInt64)
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
    throw s!"race fixture requires x86_64-unknown-linux-gnu; triple={compiler.program.input.producer.targetTriple}, arch={arch}, bits={targetBits}"
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
      | .error (error, state) => throw s!"canonical callback construction failed: {reprStr error}; {raceStateInfo state}"
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
        -- Preserve the equality regressions alongside the retained graph consumer.
        -- These assertions test exact equality, independently of graph completion.
        let stateSelfEq := decide (afterCallbacks = afterCallbacks)
        let rebuiltState := {afterCallbacks with machine :=
          {afterCallbacks.machine with threads := afterCallbacks.machine.threads}}
        let rebuiltStateEq := decide (afterCallbacks = rebuiltState)
        let tapeBeforeSmoke := choiceAccess.get afterCallbacks
        let changedLedgerState := choiceAccess.put afterCallbacks
          {tapeBeforeSmoke with generatedChoices := tapeBeforeSmoke.generatedChoices + 1}
        let changedLedgerEq := decide (afterCallbacks = changedLedgerState)
        let world := afterCallbacks.machine.user.user.payload.payload
        let source := world.types.metadata.source
        let withSource := fun (changedSource : Input.ImportDocumentCore)
            (nodeCache : Option (Input.RuntimeNodeLookupCache changedSource.types)) =>
          let changedMetadata := {world.types.metadata with source := changedSource, nodeCache}
          let changedTypes := {world.types with metadata := changedMetadata}
          let changedWorld := {world with types := changedTypes}
          let changedValidity := {afterCallbacks.machine.user.user with
            payload := {afterCallbacks.machine.user.user.payload with payload := changedWorld}}
          let changedStorage := {afterCallbacks.machine.user with user := changedValidity}
          {afterCallbacks with machine := {afterCallbacks.machine with user := changedStorage}}
        -- A changed shared-node array cannot retain its old dependent ABI cache.
        let changedSharedNodesState := withSource
          {source with
            sharedNodes := source.sharedNodes.push Lean.Json.null
            compilerFunctionAbiTable := none} world.types.metadata.nodeCache
        let changedSharedNodesEq := decide (afterCallbacks = changedSharedNodesState)
        unless source.raw != Lean.Json.null do
          throw "fixture unexpectedly has a null source document"
        let changedRawState := withSource {source with raw := Lean.Json.null}
          world.types.metadata.nodeCache
        let changedRawEq := decide (afterCallbacks = changedRawState)
        let timestampRead := Miri.Concurrency.VTimestamp.ofPacked 2 (by decide)
        let timestampRetag := Miri.Concurrency.VTimestamp.ofPacked 3 (by decide)
        let timestampSameTime := Miri.Concurrency.VTimestamp.sameTime timestampRead timestampRetag
        let timestampExactEq := decide (timestampRead = timestampRetag)
        unless stateSelfEq && rebuiltStateEq && !changedLedgerEq && !changedSharedNodesEq &&
            !changedRawEq && timestampSameTime && !timestampExactEq do
          throw s!"exact equality runtime smoke failed: self={stateSelfEq}; rebuilt={rebuiltStateEq}; changed_generated={changedLedgerEq}; changed_shared_nodes={changedSharedNodesEq}; changed_raw={changedRawEq}; timestamp_same_time={timestampSameTime}; timestamp_exact={timestampExactEq}"
        let graph := exploreConnected loop choiceAccess afterCallbacks nodeBudget
        pure s!"canonical_source_route=makeFromSourcePackage+callbackBuilder+MiriConnected+hooksFromSource\nequality_smoke=self_eq={stateSelfEq};rebuilt_eq={rebuiltStateEq};changed_generated_eq={changedLedgerEq};changed_shared_nodes_eq={changedSharedNodesEq};changed_raw_eq={changedRawEq};timestamp_same_time={timestampSameTime};timestamp_exact_eq={timestampExactEq}\nsource_entry=miri_start; scheduler=fixedScheduling_false; foreign=canonical Unix/Pthread\n{renderGraphReport graph}"

def mainWithEq [DecidableEq OuterState] (args : List String) : IO Unit := do
  let some input := args.head? | throw (IO.userError "usage: ConnectedGraph215 <untouched-export.json> [node-budget]")
  unless (args.length == 1 || args.length == 2 || args.length == 5) do
    throw (IO.userError "usage: ConnectedGraph215 <input> [node-budget [page-size num-cpus pid]]")
  let nodeBudget ← match (args.drop 1).head? with
    | none => pure 10000
    | some raw => do
      let some value := raw.toNat? | throw (IO.userError "node budget must be a natural number")
      if value == 0 || value > 1000000 then throw (IO.userError "node budget must be between 1 and 1000000")
      pure value
  let contents ← IO.FS.readFile input
  let (pageSize, numCpus, hostPid) ← match args.drop 2 with
    | [] => do
      let (pageSize, numCpus) ← captureLinuxProfile
      let hostPid ← IO.Process.getPID
      pure (pageSize, numCpus, hostPid)
    | [rawPage, rawCpu, rawPid] => do
      let some page := rawPage.toNat? | throw (IO.userError "invalid page size")
      let some cpu := rawCpu.toNat? | throw (IO.userError "invalid CPU count")
      let some pid := rawPid.toNat? | throw (IO.userError "invalid PID")
      unless page > 0 && page < 2^64 && cpu > 0 && cpu < 2^32 && pid < 2^32 do
        throw (IO.userError "host profile outside supported range")
      pure (UInt64.ofNat page, UInt32.ofNat cpu, UInt32.ofNat pid)
    | _ => throw (IO.userError "incomplete host profile")
  let report ← match runScLitmusPure contents nodeBudget pageSize numCpus hostPid with
    | .ok report => pure report
    | .error error => throw (IO.userError error)
  IO.println s!"{report}\nhost_profile=page_size={pageSize.toNat};num_cpus={numCpus.toNat};pid={hostPid.toNat}"

def main (args : List String) : IO Unit := by
  letI : DecidableEq OuterState := ExactEqualityFast225.outerStateDecidableEqFast
  exact mainWithEq args
