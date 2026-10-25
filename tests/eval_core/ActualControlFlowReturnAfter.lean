import Miri.Input.EvalConfigurationCore
import Miri.Input.CompilerGlobals
import Miri.Input.CompilerFunctionPointers
import Miri.Input.CompilerVTableMachine
import Miri.Input.CompilerIntrinsicSymbols
import Miri.Input.EvalCompilerMachine
import Miri.Input.EvalRuntimeConstruction
import Miri.Input.EvalTerminatorMachine

/-! Real exported generic-call/loop execution through the root's normal
Return terminator. The prefix reaches root Return after nested calls, executes
that source step, checks normal root cleanup leaves an empty stack, then reads
the now initialized caller return place before any stack-empty callback. -/
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
private abbrev Host := Input.HostRuntime.Storage Unit Unit Unit Unit Unit String Unit Unit
private abbrev World := Input.EvalWorld.World Unit Unit Unit Unit Unit String Unit Unit Host
private abbrev CoreUser := Input.EvalCoreMachine.User Unit Unit Unit Unit Unit String Unit Unit Host
private abbrev EntryUser := Input.EvalExecutable.U Unit Unit Unit Unit Unit String Unit Unit Host
private abbrev InnerState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Inner World)
private abbrev OuterState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Outer World)
private abbrev CoreOptions := Input.EvalConfigurationCore.Options
private abbrev CoreLeaves := Input.EvalConfigurationCore.Leaves
  Unit Unit Unit Unit Unit String Unit Unit Host Unit Unit
private abbrev LoopHooks := RunLoopHooks OuterState Unit MainMachine.Callback

private def must {A : Type} (value : Except String A) : IO A :=
  match value with
  | .ok result => pure result
  | .error reason => throw (IO.userError reason)

private def checkedState {S A : Type} (result : StepResult S A) : Except String (S × A) :=
  match result with
  | (state, .ok value) => .ok (state, value)
  | (_, .error error) => .error s!"source prefix failed: {reprStr error}"

private def options : CoreOptions := {
  place := {debugAssertions := false, dynamicFuel := 256, validation := .Shallow}
  limits := {callDispatch := 128, casts := 128, retag := 128, validation := 128}
  compatibilityBudget := 128, varArgsBudget := 128, callbackCapacity := 128
  floatNondeterministic := false, weakFailureRate := 0, crossCrateInlineAlways := false
  userRelevantCrates := #[], ignoreOptionalOverflowChecks := false, panicUnwinds := true
  retag := {implicitWrites := false, preciseInteriorMut := true} }

private def unknownSync : Unit → Concurrency.SyncObject.AccessKind →
    PlaceMachine.MachineM MiriMemoryKind CoreUser Unit :=
  fun _ _ => fun machine => .error (.unsupported "sync payload access unavailable in isolated smoke") machine

private def leaves (dummy : SpanRef) : CoreLeaves := {
  pointerSource := {
    nativeLibraryPaths := fun host => host.nativeLibraries.map Prod.fst
    nativeHost := none

  }
  sync := unknownSync
  storage := fun size _ => some (Array.replicate size.bytes.toNat 0)
  spans := ⟨dummy, false⟩
  foreign := none
  dynSymName := fun _ => ""
  checkLlvmSymbolClash := fun _ => throw (.unsupported "LLVM symbol registry unavailable in isolated smoke")
  math := none
  mathError := .none
  control := Input.EvalTerminatorMachine.controlAccess
  blockingSources := Input.EvalTerminatorMachine.ioSourcesAccess }

private def rootCall (p : Input.CompilerProviders.Prepared) (body : LoadedBody)
    (rootInstance : CallInstance) (config : ExecutionMachine.Config MiriMemoryKind
      CoreUser Unit String ABI.ExternAbi Unit) (state : InnerState) :
    Except String (InnerState × RuntimeStackPlace Provenance) := do
  let abi ← Input.CompilerInstanceAbi.abiOfInstance p.lifecycle.instances rootInstance #[]
  let some returnTy := body.body.locals[0]? | throw "root has no return local"
  let returnLayout ← (p.runtime.lookup returnTy).mapError toString
  let hooks := ExecutionMachine.callHooks config options.limits
  let action : MachineHooks.M MiriMemoryKind CoreUser
      (RuntimeStackPlace Provenance) := do
    let destination ← hooks.allocateStack () returnLayout
    Call.initStackFrame hooks () rootInstance body abi #[] false (.memory destination) (.stop true)
    pure (.memory destination)
  checkedState (MachineHooks.run action state)

private def absentLoopHooks : LoopHooks := Id.run do
  let absent : StepError := .unsupported "stack-empty/main callbacks are unavailable in this finite prefix"
  let coreStep : Unit → OuterState → StepResult OuterState Bool := fun _ state => (state,.error absent)
  let takeStackEmptyCallback : OuterState → StepResult OuterState MainMachine.Callback :=
    fun state => (state,.error absent)
  let invokeStackEmptyCallback : Unit → MainMachine.Callback → OuterState →
      StepResult OuterState StackEmptyPoll := fun _ _ state => (state,.error absent)
  let restoreStackEmptyCallback : MainMachine.Callback → OuterState → StepResult OuterState Unit :=
    fun _ state => (state,.error absent)
  let terminateActiveThread : Unit → Bool → OuterState → StepResult OuterState Unit :=
    fun _ _ state => (state,.error absent)
  return {
    coreStep, takeStackEmptyCallback, invokeStackEmptyCallback, restoreStackEmptyCallback
    terminateActiveThread, interrupted := fun _ => false
    handleAbnormalTermination := id
    schedule := fun _ state => (state,.ok .executeStep)
    communicate := fun _ => false
    pollAndUnblock := fun _ _ state => (state,.error absent)
    sleep := fun _ _ state => (state,.error absent) }

private def absentScheduler : Unit → ThreadStacks.LocalSchedulerHooks MiriMemoryKind EntryUser :=
  fun _ => Id.run do
    let absent : StepError := .unsupported "local scheduler host callback is unavailable in this prefix"
    return {
      processDelayedReadiness := fun state => .error absent state
      communicate := fun state => .error absent state
      pollHostIoNonBlocking := fun state => .error absent state
      unblockExpiredDeadlines := fun state => .error absent state
      choose := fun _ state => .error absent state
      anyThreadBlockedOnHost := fun state => .error absent state }

private def atRootReturn (body : LoadedBody) (rootFnInstance : CallInstance) : OuterState → Bool :=
  fun state => match state.stack.currentFrame? with
  | none => false
  | some frame =>
    frame.bodyIdentity == body.identity && frame.functionInstance == rootFnInstance &&
    match frame.location with
    | .unwinding _ => false
    | .mir location =>
      match frame.body.basicBlocks[location.block]? with
      | none => false
      | some block => location.statementIndex == block.statements.size &&
          block.terminator.kind == .Return

private def runWithConfig (prepared : Input.CompilerProviders.Prepared)
    (body : LoadedBody) (rootInstance : CallInstance) (inner : InnerState)
    (image : Input.AllocationImage.Imported)
    (config : ExecutionMachine.Config MiriMemoryKind CoreUser Unit String ABI.ExternAbi Unit) :
    Except String String := do
  let registryAttach : MachineHooks.M MiriMemoryKind CoreUser Unit := do
    Input.CompilerFunctionPointers.attach prepared.pointers image config.functions
    let vtableRuntime := Input.EvalCompilerMachine.vtables prepared image config.functions
    Input.CompilerVTableMachine.attach prepared.vtables image vtableRuntime
    Input.CompilerIntrinsicSymbols.attach prepared image Input.EvalConfiguration.symbols
  let (inner, _) ← checkedState (MachineHooks.run registryAttach inner)
  let (inner, returnPlace) ← rootCall prepared body rootInstance config inner
  unless (match returnPlace with | .memory _ => true | _ => false) do
    throw "non-unit root return place was not backed by real memory"
  let ready : OuterState := ExecutionStateTransport.outward inner
  let configs : Unit → Input.EvalExecutable.Core Unit Unit Unit Unit Unit String Unit Unit Host Unit Unit :=
    fun _ => config
  let stop := atRootReturn body rootInstance
  let (beforeReturn, _) ← checkedState (Input.EvalRuntimeConstruction.runReadyConfiguredPrefixUntil
    configs options.limits absentLoopHooks absentScheduler stop (List.replicate 128 ()) ready)
  unless stop beforeReturn do
    throw "source nested-call/loop prefix exhausted choices before the root Return terminator"
  let some rootFrame := beforeReturn.stack.currentFrame? | throw "root caller frame vanished before its Return"
  unless rootFrame.returnPlace == returnPlace && rootFrame.bodyIdentity == body.identity &&
      rootFrame.functionInstance == rootInstance do
    throw "source call return lost the root frame, full instance, or real destination"
  let loop := Input.EvalExecutable.fixedCorePrefixLoop configs options.limits
    absentLoopHooks absentScheduler
  let (afterReturn, _) ← checkedState (RunLoop.iteration loop () beforeReturn)
  unless afterReturn.stack.frames.isEmpty do
    throw "normal root Return did not leave an empty source stack"
  unless afterReturn.stack.currentFrame?.isNone do
    throw "normal root Return unexpectedly retained an active frame"
  let .memory destination := returnPlace | throw "root result did not retain its real memory destination"
  let resultOp : OpTy Provenance := ⟨.indirect destination.mplace, destination.layout⟩
  let (_, value) ← checkedState (MachineHooks.run
    (PlaceMachine.readImmediate config.access resultOp) (ExecutionStateTransport.inward afterReturn))
  let scalar ← (value.imm.toScalar.mapError reprStr)
  let result ← (scalar.toUInt32.mapError reprStr)
  unless result == 9 do throw s!"generic call/loop returned {result}, expected 9"
  unless (prepared.program.instances.size > 0) do
    throw "export did not retain any compiler instance graph entries"
  pure s!"actual exported generic calls and loop returned {result}; normal root Return emptied stack; instance-graph={prepared.program.instances.size}"

private def runPrepared (prepared : Input.CompilerProviders.Prepared) : Except String String := do
  let dummy ← Input.CompilerContextSpan.rootSpan prepared.program
  let definition ← prepared.program.rootDefinitionId 0
  let rootInstance : CallInstance := ⟨.Item definition, #[]⟩
  let body ← Input.CallResolution.loadedBodyOfInstance prepared.lifecycle.calls.calls rootInstance
  let imported := Input.CompilerGlobals.importGraph prepared.runtime.target prepared.program
    (MemoryState.empty : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
  let image ← imported.outcome
  let arrays ← prepared.initialArrays
  let host : Host := {
    blocking := ⟨none, #[]⟩, clock := .virtual 0, deadlines := .empty
    readiness := {}, futex := {}, sync := {}, io := {}, events := #[]
    virtualSockets := #[], tcpSockets := #[], nativeLibraries := #[], profiler := none
    control := TerminatorControl.initial ⟨0, 0x3f847ae147ae147b, true⟩ }
  let arch ← Input.EvalArchitectureMachine.targetArch prepared.intrinsics
  let targetBits := prepared.runtime.target.base.pointerWidth.bits.toNat
  let targetTriple := prepared.program.input.producer.targetTriple
  unless targetTriple == "x86_64-unknown-linux-gnu" && arch == "x86_64" && targetBits == 64 do
    throw s!"fixture target differs from this source runner setup: triple={targetTriple}, arch={arch}, pointer_bits={targetBits}"
  let geometry ← (Input.InitialMachine.geometry targetBits arch false none).mapError reprStr
  let machineConfig : Input.InitialMachine.Configuration Unit Unit := {
    geometry, dummySpan := dummy, provenance := .default, addressMode := .managed
    addressStop := 18446744073709551615, addressReuse := ⟨0.5, 0.1⟩
    fixedScheduling := true, trackOutdatedLoads := false, weakMemory := true
    backend := .vclocks, trackedTags := some #[], validation := .Shallow
    alignment := .Int, affinity := none, muteOutput := true, hostUsizeBits := 64 }
  let initial ← (Input.InitialMachine.create (Os := Unit) (R := Unit) (P := Unit)
    (H := Unit) (D := Unit) (O := String) (Aff := Unit) (B := Unit)
    machineConfig imported.memory arrays
      { inputs := #[Miri.Interpreter.ExecutionChoices.Input.index (Miri.Interpreter.ExecutionChoices.IndexSite.addressSlack) 0,
  Miri.Interpreter.ExecutionChoices.Input.boolean
    (Miri.Interpreter.ExecutionChoices.BoolSite.addressReuse)
    false,
  Miri.Interpreter.ExecutionChoices.Input.index (Miri.Interpreter.ExecutionChoices.IndexSite.addressSlack) 0], cursor := 0, policy := .strict } host).mapError reprStr
  let initial : OuterState := initial
  let inner := ExecutionStateTransport.inward initial
  let bytesAction : MachineHooks.M MiriMemoryKind CoreUser
      Input.CompilerGlobalBytes.Prepared :=
    Input.CompilerGlobalBytes.attach prepared.program prepared.runtime
  let (inner, bytes) ← checkedState (MachineHooks.run bytesAction inner)
  let coreLeaves := leaves dummy
  match Input.EvalConfigurationCore.make prepared image bytes options coreLeaves () 256 with
  | .error error => .error (reprStr error)
  | .ok config => runWithConfig prepared body rootInstance inner image config

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "actual pinned-export JSON required")
  let decoded ← must (Input.decodeJson (← IO.FS.readFile path))
  unless decoded.executionInput.isSome do
    throw (IO.userError "pinned export has unresolved source execution-input readiness")
  let program ← must (Input.lowerProgram decoded.document)
  let prepared ← must (Input.CompilerProviders.prepare program)
  IO.println (← must (runPrepared prepared))
