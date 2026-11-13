import MiriTests.Connected.Proofs.ExactStateCodec207
import Miri.Input.CompilerInitialAllocationPreparation
import Miri.Input.ProfileDocument
import Miri.Input.ProfilePreparation
import Miri.Input.ProfileRuntime
import Miri.Input.CompilerInitialAllocationBytes
import Miri.Input.EvalConfigurationCore
import Miri.Input.CompilerGlobals
import Miri.Input.CompilerAllocIdWorld
import Miri.Input.CompilerFunctionPointers
import Miri.Input.CompilerVTableMachine
import Miri.Input.CompilerIntrinsicSymbols
import Miri.Input.EvalCompilerMachine
import Miri.Input.EvalTerminatorMachine

/-! Check the cached-u32 runtime profile's rejection boundaries. A malformed
cached scalar width rejects preparation. Promoted and cold raw operands return
Unsupported while preserving the complete current state after a stack reserve.
Input uses the same zero-argument u32 caller and initial memo as the runtime check.
Usage: lean --run tools/check-initial-ctfe-rejections.lean <export.json> -/
set_option synthInstance.maxSize 4096

open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter
private abbrev Host := Input.HostRuntime.Storage Unit Unit Unit Unit Unit String Unit Unit
private abbrev World := Input.EvalWorld.World Unit Unit Unit Unit Unit String Unit Unit Host
private abbrev CoreUser := Input.EvalCoreMachine.User Unit Unit Unit Unit Unit String Unit Unit Host
private abbrev InnerState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Inner World)
private abbrev OuterState := MachineHooks.State MiriMemoryKind
  (ExecutionStateTransport.Outer World)
private abbrev CoreOptions := Input.EvalConfigurationCore.Options
private abbrev CoreLeaves := Input.EvalConfigurationCore.Leaves
  Unit Unit Unit Unit Unit String Unit Unit Host Unit Unit

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
  fun _ _ => fun machine => .error (.unsupported "sync payload access unavailable in bounded runtime control") machine

private def leaves (dummy : SpanRef) : CoreLeaves := {
  constQueries := .cachedOnly
  pointerSource := {
    nativeLibraryPaths := fun host => host.nativeLibraries.map Prod.fst
    nativeHost := none

  }
  sync := unknownSync
  storage := fun size _ => some (Array.replicate size.bytes.toNat 0)
  spans := ⟨dummy, false⟩
  foreign := none
  dynSymName := fun _ => ""
  checkLlvmSymbolClash := fun _ => throw (.unsupported "LLVM symbol registry unavailable in bounded runtime control")
  math := none
  mathError := .none
  control := Input.EvalTerminatorMachine.controlAccess
  blockingSources := Input.EvalTerminatorMachine.ioSourcesAccess }

private def rootCall (p : Input.CompilerProviders.Prepared) (body : LoadedBody)
    (rootInstance : CallInstance) (config : ExecutionMachine.Config MiriMemoryKind
      CoreUser
      Unit String ABI.ExternAbi Unit) (state : InnerState) : Except String (InnerState × RuntimeStackPlace Provenance) := do
  let abi ← Input.CompilerInstanceAbi.abiOfInstance p.lifecycle.instances (Input.EvalProjectionMachine.arrays.get state) rootInstance #[]
  let some returnTy := body.body.locals[0]? | throw "root has no return local"
  let returnLayout ← (p.runtime.lookup returnTy).mapError toString
  let hooks := ExecutionMachine.callHooks config options.limits
  let action : MachineHooks.M MiriMemoryKind
      CoreUser
      (RuntimeStackPlace Provenance) := do
    let destination ← hooks.allocateStack () returnLayout
    Call.initStackFrame hooks () rootInstance body abi #[] false (.memory destination) (.stop true)
    pure (.memory destination)
  checkedState (MachineHooks.run action state)

/-- Compare the complete executable state structurally. Refresh only Store's
run/crosswalk views from the authoritative current MemoryState on each side;
this refresh is part of callback attachment, not an allocation/memo effect. -/
private def normalizeStore (state : InnerState) : InnerState :=
  match Input.EvalWorld.initialCompilerStoreInnerAccess.getStore state.machine.user with
  | none => state
  | some store =>
    let current := (store.withMemory state.machine.memory).store
    {state with machine := {state.machine with user :=
      Input.EvalWorld.initialCompilerStoreInnerAccess.setStore current state.machine.user}}

private def preserves (before after : InnerState) : Bool :=
  decide (normalizeStore before = normalizeStore after)

private def expectRejection (prepared : Input.CompilerProviders.Prepared) (image : Input.AllocationImage.Imported)
    (operand : ConstOperand) (reason : String) (state : InnerState) : Except String Unit := do
  let (after,outcome) := MachineHooks.run
    (Input.RuntimeCtfeQueryMachine.evaluate .cachedOnly prepared image Input.EvalProjectionMachine.arrays
      Input.EvalWorld.initialCompilerStoreInnerAccess Input.EvalWorld.initialCompilerQueryInnerAccess
      Input.CompilerTypingEnv.fullyMonomorphized operand) state
  match outcome with
  | .error (.unsupported actual) =>
    unless actual == reason do
      throw s!"wrong Unsupported diagnostic: {actual}"
  | .error error => throw s!"wrong error class: {reprStr error}"
  | .ok _ => throw "negative runtime query unexpectedly succeeded"
  unless preserves state after do throw "rejection lost/changed current allocation prefix, arena, Store or memo"

private def runPrepared (profile : Input.ProfilePreparation.Prepared)
    (prepared : Input.CompilerProviders.Prepared)
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind)
    (image : Input.AllocationImage.Imported) (initialTypes : Input.RuntimeArrayTypes.World)
    (byteView : Input.CompilerGlobalBytes.Prepared) (cold : Bool) : Except String String := do
  let dummy ← Input.CompilerContextSpan.rootSpan prepared.program
  let definition ← prepared.program.rootDefinitionId 0
  let (rootInstance,initialTypes) ← (Input.RuntimeArrayTypes.performCompiler initialTypes
    (Input.CompilerInstance.item definition #[])).mapError reprStr
  let (body,arrays) ← (Input.RuntimeArrayTypes.performCompiler initialTypes
    (Input.CallResolution.loadedBodyOfInstance prepared.lifecycle.calls.calls rootInstance)).mapError reprStr
  let some returnTy := body.body.locals[0]? | throw "root has no return local"
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
  let dummySpan := dummy
  let machineConfig : Input.InitialMachine.Configuration Unit Unit := {
    geometry, dummySpan, provenance := .default, addressMode := .managed
    addressStop := 18446744073709551615, addressReuse := ⟨0.5, 0.1⟩
    fixedScheduling := false, trackOutdatedLoads := false, weakMemory := true
    backend := .vclocks, trackedTags := some #[], validation := .Shallow
    alignment := .Int, affinity := none, muteOutput := true, hostUsizeBits := 64 }
  -- Finite actual source address choices for this stack-allocation prefix.
  -- Any other source choice site or tape exhaustion remains an execution error.
  let initial ← (Input.InitialMachine.create (Os := Unit) (R := Unit) (P := Unit)
    (H := Unit) (D := Unit) (O := String) (Aff := Unit) (B := Unit)
    machineConfig memory arrays
      { inputs := Array.replicate 128 (.index .addressSlack 0), cursor := 0 } host).mapError reprStr
  let initial : OuterState := initial
  let initial ← (Input.ProfileRuntime.installStoreState Input.EvalWorld.initialCompilerStoreAccess profile initial).mapError reprStr
  let initial ← (Input.ProfileRuntime.installQueriesState Input.EvalWorld.initialCompilerQueryAccess profile initial).mapError reprStr
  let inner := ExecutionStateTransport.inward initial
  let bytesAction : MachineHooks.M MiriMemoryKind
      CoreUser
      Input.CompilerGlobalBytes.Prepared :=
    do
      modify fun state => {state with machine := {state.machine with memory :=
        {state.machine.memory with byteGlobalKeys := byteView.keys,byteGlobalKeysReady := true}}}
      pure byteView
  let (inner, bytes) ← checkedState (MachineHooks.run bytesAction inner)
  let coreLeaves := leaves dummy
  match Input.EvalConfigurationCore.make prepared image bytes options coreLeaves () 256 with
  | .error error => throw (reprStr error)
  | .ok config => do
    let registryAttach : MachineHooks.M MiriMemoryKind
        CoreUser Unit := do
      Input.CompilerFunctionPointers.attach prepared.pointers image config.functions
      let vtableRuntime := Input.EvalCompilerMachine.vtables prepared image config.functions
      Input.CompilerVTableMachine.attach prepared.vtables image vtableRuntime
      Input.CompilerIntrinsicSymbols.attach prepared image Input.EvalConfiguration.symbols
    let (inner, _) ← checkedState (MachineHooks.run registryAttach inner)
    -- Preserve a genuine pre-existing stack allocation, including uninitialized
    -- bytes, provenance and borrow permissions, across the rejected query.
    let action : MachineHooks.M MiriMemoryKind CoreUser ConstOperand := do
      let actual ← Input.RuntimeArrayQueries.performCompiler Input.EvalProjectionMachine.arrays
        (prepared.program.resolveBodyIdentity body.identity)
      let some constant := actual.input.requiredConsts[0]?
        | throw (.invalidProgram "actual raw required_const absent")
      let some returnTy := body.body.locals[0]? | throw (.invalidProgram "return local absent")
      let layout ← Input.RuntimeArrayQueries.layoutOf Input.EvalProjectionMachine.arrays returnTy
      let _ ← (ExecutionMachine.callHooks config options.limits).allocateStack () layout
      pure constant
    let (inner,constant) ← checkedState (MachineHooks.run action inner)
    unless !inner.machine.memory.live.isEmpty do throw "failure-prefix control did not retain a genuine allocation"
    let .Unevaluated raw declared := constant.value | throw "actual source operand was evaluated/erased"
    if cold then
      expectRejection prepared image constant
        s!"runtime CTFE operand at span {constant.span.id}: selected VALUE miss requires source trivial_const/nontrivial evidence; an allocation memo alone does not choose the compiler VALUE dependency path" inner
    else
      let promoted := {constant with value := .Unevaluated {raw with promoted := some 0} declared}
      expectRejection prepared image promoted
        "runtime Unevaluated is outside empty-argument/unpromoted empty-ParamEnv domain" inner
    pure s!"PASS runtime {if cold then "cold" else "promoted"} Unsupported; live allocation/type universe/Store/memo prefix retained"

private def put (object : Lean.Json) (field : String) (value : Lean.Json) : Except String Lean.Json := do
  let fields := (← object.getObj?).toArray
  unless fields.any (fun row => row.1 == field) do throw s!"missing mutation field {field}"
  pure (Lean.Json.mkObj (fields.toList.map fun (name,old) => (name,if name == field then value else old)))

private def changeTable (document : Lean.Json) (width : Bool) : Except String Lean.Json := do
  let tables ← (← document.getObjVal? "compiler_initial_selected_query_cache").getArr?
  let [table] := tables.toList | throw "expected one actual selected table"
  let slots ← (← table.getObjVal? "slots").getArr?
  let slots ← slots.mapM fun slot => do
    if !width then return ← put (← put slot "present" (.bool false)) "result" .null
    let key ← slot.getObjVal? "key"
    if (← key.getObjValAs? String "family") != "value" || !(← slot.getObjValAs? Bool "present") then return slot
    let result ← slot.getObjVal? "result"
    let value ← result.getObjVal? "value"
    put slot "result" (← put result "value" (← put value "size_bytes" (Lean.toJson (8 : Nat))))
  let table ← put table "slots" (.arr slots)
  let table ← if width then pure table else do
    let mut membership ← table.getObjVal? "membership"
    for field in ["codegen_value_present","codegen_allocation_present","post_analysis_value_present","post_analysis_allocation_present"] do
      membership ← put membership field (.bool false)
    put table "membership" membership
  put document "compiler_initial_selected_query_cache" (.arr #[table])

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected actual cached runtime document")
  let text ← IO.FS.readFile path
  let raw ← must (Lean.Json.parse text)
  let malformed ← must (changeTable raw true)
  let decoded ← must (Input.ProfileDocument.decodeProfiled malformed.compress {})
  let widthAttempt := Input.ProfilePreparation.prepareProfiled {} (text.utf8ByteSize+1) 1 decoded
  match widthAttempt.outcome with
  | .error reason => unless reason == "selected initial memo requires u32 ScalarInt, not another ConstValue" do
      throw (IO.userError s!"wrong cached-width rejection: {reason}")
  | .ok _ => throw (IO.userError "cached wrong width admitted")
  IO.println "PASS cached ScalarInt wrong width rejected before runtime provider installation"
  for cold in [false,true] do
    let source ← if cold then pure (← must (changeTable raw false)).compress else pure text
    let decoded ← must (Input.ProfileDocument.decodeProfiled source {})
    let attempt := Input.ProfilePreparation.prepareProfiled {} (source.utf8ByteSize+1) 1 decoded
    let profile ← must attempt.outcome
    let .initial material roots selected := profile | throw (IO.userError "wrong profile")
    unless roots.isEmpty && selected.memos.size == 1 do throw (IO.userError "wrong selected catalogue")
    let bytes ← must (Input.ProfileRuntime.bytes profile attempt.memory)
    IO.println (← must (runPrepared profile material.compiler attempt.memory material.image material.types bytes cold))
