import Miri.Interpreter.Call
open Miri Miri.ABI Miri.Memory Miri.Interpreter
namespace CallTests

def layout : LocalLayout := ⟨0, {
  fields := .Primitive, variants := .Single 0, backendRepr := .Memory (sized := true),
  largestNiche := none, uninhabited := false, align := .new Align.ONE,
  size := Size.ZERO, maxReprAlign := none, unadjustedAbiAlign := Align.ONE,
  reprC := false, randomizationSeed := 0 }⟩
def op : OpTy Unit := ⟨.immediate .uninit, layout⟩
def mplace : MPlaceTy Unit := ⟨⟨⟨Size.ZERO, some ()⟩, .none, none⟩, layout⟩
def fixtureIdentity : LocalsIdentity := (LocalsIdentitySupply.allocate ⟨0⟩).2
def runtimePlace : RuntimeStackPlace Unit := .frameLocal 0 0 none layout fixtureIdentity
def body : MIR.Body := ⟨.Built, 1, none, #[0, 0], #[]⟩
def fixtureBodies : Array MIR.Body := #[body, { body with spreadArgument := some 1 }]
def loaded (key : Fin fixtureBodies.size) : LoadedBody :=
  ⟨BodyIdentity.ofCanonicalIndex key.val, fixtureBodies[key]⟩
def frame : Frame Unit LocalLayout Unit := Frame.create (loaded ⟨0, by decide⟩) ⟨.Item 0, #[]⟩ () (.stop true) runtimePlace ⟨0⟩ fixtureIdentity
structure TestAbi where
  args : Array LocalLayout
  ret : LocalLayout
  canUnwind : Bool
  variadic : Bool
  fixed : Nat
structure State where
  frame : Frame Unit LocalLayout Unit := frame
  trace : List String := []
  index : Nat := 0
  localsSupply : LocalsIdentitySupply := ⟨1⟩

def log (name : String) (value : A) : CallM State A := do
  modify fun s => { s with trace := s.trace ++ [name] }
  pure value
def blocked (name : String) : CallM State A := do
  let _ ← log name ()
  throw (.unsupported name)
abbrev Hooks := CallHooks Unit State Unit Unit Unit Bool TestAbi LocalLayout

def hooks : Hooks := {
  debugAssertions := false
  getFrame := return (← get).frame
  setFrame := fun f => modify fun s => { s with frame := f }
  frameIndex := return (← get).index
  evalOperand := fun _ _ => log "operand" op
  evalPlace := fun _ _ skip => log s!"place:{skip}" runtimePlace
  placeToOp := fun _ _ => log "placeToOp" op
  forceAllocation := fun _ _ => log "forceAllocation" mplace
  functionSignature := fun _ _ => log "signature" (1, false)
  functionKind := fun _ => log "functionKind" (.FnDef 0 #[])
  readPointer := fun _ _ => blocked "readPointer"
  getPtrFn := fun _ _ => blocked "getPtrFn"
  resolve := fun _ _ _ => log "resolve" ⟨.Item 0, #[]⟩
  fnAbiOfFnPtr := fun _ _ _ => blocked "fnAbiOfFnPtr"
  fnAbiOfInstance := fun _ _ _ => log "fnAbi" ⟨#[layout], layout, true, false, 1⟩
  requiresCallerLocation := fun _ => log "requiresLocation" false
  callerLocation := blocked "callerLocation"
  abiCanUnwind := (·.canUnwind)
  abiVariadic := (·.variadic)
  abiFixedCount := (·.fixed)
  abiArgs := (·.args)
  abiReturn := (·.ret)
  sameConvention := fun _ _ => true
  isRustCall := id
  rustAbi := false
  argLayout := id
  argIsIgnore := fun _ => true
  isOneZst := fun _ => true
  checkArgumentCompat := fun _ _ _ => log "compat" true
  checkTargetFeatures := fun _ _ => log "targetFeatures" ()
  tupleFields := fun _ => log "tupleFields" #[0]
  projectFnArg := fun _ arg _ => log "projectField" arg
  localLayout := fun _ _ => log "localLayout" layout
  localSpan := fun _ _ => pure ⟨0⟩
  storageLiveDyn := fun _ _ _ => log "storageLive" ()
  copyAllowTransmute := fun _ _ _ => log "copy" ()
  protectArgument := fun _ _ => log "protect" ()
  withRetagMode := fun _ mode action => do
    let _ ← log s!"retag:{reprStr mode}" ()
    let result ← action
    let _ ← log "restoreRetag" ()
    pure result
  nonCapturingClosure := fun _ _ _ => log "nonCapturing" false
  allocateStack := fun _ _ => blocked "allocateStack"
  copyToMemory := fun _ _ _ => blocked "copyToMemory"
  vaListPtr := fun _ _ => blocked "vaListPtr"
  writeZeroBytes := fun _ _ _ => blocked "writeZeroBytes"
  vaListKeyField := fun _ _ => blocked "vaListKeyField"
  writePointerToMemory := fun _ _ _ => blocked "writePointerToMemory"
  pushRaw := fun _ inst b dest cont => do
    let _ ← log "pushRaw" ()
    modify fun s =>
      let (supply, identity) := s.localsSupply.allocate
      { s with
        frame := Frame.create b inst () cont dest ⟨0⟩ identity
        index := s.index + 1
        localsSupply := supply }
  pushDone := fun _ => log "pushDone" ()
  popRaw := fun _ => do
    let _ ← log "popRaw" ()
    let s ← get
    modify fun s => { s with index := s.index - 1 }
    pure s.frame
  cleanup := fun _ _ _ => log "cleanup" .normal
  afterFrameInit := fun _ => log "afterFrameInit" ()
  callExtra := fun _ _ _ _ _ _ _ => blocked "callExtra"
  callIntrinsic := fun _ _ _ _ _ _ => blocked "callIntrinsic"
  callLlvmIntrinsic := fun _ _ _ _ _ => blocked "callLlvmIntrinsic"
  findMirOrEvalFn := fun _ inst _ _ _ _ _ => log "findMir" (some (loaded ⟨0, by decide⟩, inst))
  resolveVirtual := fun _ _ _ _ _ _ => blocked "resolveVirtual"
  isDynamic := fun _ => blocked "isDynamic"
  unpackDynForDrop := fun _ _ => blocked "unpackDynForDrop"
  resolveDropGlue := fun _ _ => blocked "resolveDropGlue"
  mplaceToMutRef := fun _ _ => blocked "mplaceToMutRef"
  fakeUnitReturn := fun _ => blocked "fakeUnitReturn" }
end CallTests
open CallTests
open Miri.Interpreter

def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

example : (CallShimKind.ClosureOnce 7 9 true).defId = 7 := rfl
example : (CallShimKind.ConstructCoroutineInClosure 11 true).defId = 11 := rfl
example : (CallInstanceKind.Shim (.DropGlue 13 (some 15))).defId = 13 := rfl
example : (CallInstanceKind.Virtual 17 19).defId = 17 := rfl

def main : IO Unit := do
  -- Compare source's four Move-disjoint paths and ordinary copy.
  for disjoint in [false, true] do
    for indirect in [false, true] do
      let h := { hooks with
        placeToOp := fun _ _ => log "placeToOp"
          (if indirect then ⟨.indirect mplace.mplace, layout⟩ else op) }
      let (state, result) := Call.run (Call.evalFnCallArgument h () (.Move ⟨1, #[]⟩) disjoint) {}
      let .ok arg := result | throw (IO.userError "argument evaluation")
      let inPlace := match arg with | .InPlace _ => true | _ => false
      IO.println s!"A {disjoint} {indirect} {inPlace} {String.intercalate "," state.trace}"
  let (state, result) := Call.run (Call.evalFnCallArgument hooks () (.Copy ⟨1, #[]⟩) false) {}
  check result.isOk "copy"
  IO.println s!"C {String.intercalate "," state.trace}"
  for a in [:3] do
    for b in [:3] do
      for indirect in [false, true] do
        let arg : Miri.MIR.SpannedOperand := ⟨⟨0⟩, .Move ⟨a, if indirect then #[.Deref] else #[]⟩⟩
        IO.println s!"D {a} {b} {indirect} {Call.moveDefinitelyDisjoint #[arg] ⟨b, #[]⟩}"
  let (state, result) := Call.run (Call.passArgument hooks () (.InPlace mplace) layout layout 0 ⟨1, #[]⟩ 0 false) {}
  check (result.isOk && state.trace == ["compat", "storageLive", "place:false", "copy", "protect"]) "pass order"
  let failProtect := { hooks with protectArgument := fun _ _ => blocked "protect" }
  let (state, result) := Call.run (Call.passArgument failProtect () (.InPlace mplace) layout layout 0 ⟨1, #[]⟩ 0 false) {}
  check (!result.isOk && state.trace == ["compat", "storageLive", "place:false", "copy", "protect"]) "protect failure state"
  let failCompat := { hooks with checkArgumentCompat := fun _ _ _ => log "compat" false }
  let (state, result) := Call.run (Call.passArgument failCompat () (.InPlace mplace) layout layout 0 ⟨1, #[]⟩ 0 false) {}
  check (!result.isOk && state.trace == ["compat"]) "ABI mismatch before live"
  let request : CallRequest Unit Unit Bool TestAbi := ⟨.Instance ⟨.Item 0, #[]⟩, false,
    some ⟨#[layout], layout, true, false, 1⟩, #[.InPlace mplace], false, runtimePlace, some 1, .Continue⟩
  let (state, result) := Call.run (Call.initFnCall hooks () 4 request) {}
  check result.isOk "init call"
  check (state.trace == ["findMir", "requiresLocation", "fnAbi", "targetFeatures", "placeToOp", "pushRaw", "nonCapturing",
    "retag:Miri.TreeBorrows.RetagPolicy.RetagMode.FnEntry", "localLayout", "compat", "storageLive", "place:false", "copy", "protect", "restoreRetag", "compat", "afterFrameInit", "pushDone"]) "frame init source order"
  let badReturn := { hooks with checkArgumentCompat := fun _ _ _ => do
    let state ← get
    log "compat" (!state.trace.contains "restoreRetag") }
  let (state, result) := Call.run (Call.initFnCall badReturn () 4 request) {}
  check (!result.isOk && state.index == 1 && state.trace.getLast? == some "compat") "return ABI failure retains frame"
  let term : Miri.MIR.Terminator := ⟨⟨⟨0⟩, 0⟩,
    .Call (.Copy ⟨0, #[]⟩) #[⟨⟨0⟩, .Copy ⟨1, #[]⟩⟩] ⟨2, #[]⟩ (some 1) .Continue .Normal ⟨0⟩⟩
  let (state, result) := Call.run (Call.evalCallTerminator hooks () 4 term) {}
  check result.isOk "top-level Call"
  check (state.trace.take 8 == ["place:false", "operand", "operand", "signature", "functionKind", "resolve", "fnAbi", "requiresLocation"]) "destination before callee and args"
  let (state, result) := Call.run (Call.initFnCall hooks () 0 request) {}
  check (!result.isOk && state.trace.isEmpty) "runner budget exhaustion"
  -- Every source instance/shim arm goes to its corresponding dispatcher.
  let shims : Array CallShimKind := #[.VTable 0, .Reify 0 none, .FnPtr 0 0,
    .ClosureOnce 0 0 false, .ConstructCoroutineInClosure 0 false, .ThreadLocal 0,
    .FutureDropPoll 0 0 0, .DropGlue 0 none, .Clone 0 0, .FnPtrAsPtr 0 0,
    .FnPtrFromPtr 0 0, .AsyncDropGlueCtor 0 0, .AsyncDropGlue 0 0]
  for shim in shims do
    let (state, result) := Call.run (Call.initFnCall hooks () 4
      { request with callee := .Instance ⟨.Shim shim, #[]⟩ }) {}
    check (result.isOk && state.trace.head? == some "findMir" &&
      state.frame.functionInstance == ⟨.Shim shim, #[]⟩) "shim dispatch retains canonical identity"
  let fallback := { hooks with callIntrinsic := fun _ _ _ _ _ _ => log "intrinsic" (some ⟨.Item 0, #[]⟩) }
  let (state, result) := Call.run (Call.initFnCall fallback () 4
    { request with callee := .Instance ⟨.Intrinsic 0, #[]⟩ }) {}
  check (result.isOk && state.trace.take 3 == ["intrinsic", "requiresLocation", "findMir"]) "intrinsic fallback"
  let llvm := { hooks with callLlvmIntrinsic := fun _ _ _ _ _ => log "llvm" () }
  let (state, result) := Call.run (Call.initFnCall llvm () 1
    { request with callee := .Instance ⟨.LlvmIntrinsic 0, #[]⟩, callerFnAbi := none }) {}
  check (result.isOk && state.trace == ["llvm"]) "LLVM without ABI"
  let foreign := { hooks with callExtra := fun _ _ _ _ _ _ _ => log "foreign" () }
  let (state, result) := Call.run (Call.initFnCall foreign () 1 { request with callee := .Other () }) {}
  check (result.isOk && state.trace == ["foreign"]) "foreign function pointer"
  let virtual := { hooks with resolveVirtual := fun _ _ _ _ abi args => log "virtual" (⟨.Item 0, #[]⟩, abi, args) }
  let (state, result) := Call.run (Call.initFnCall virtual () 4
    { request with callee := .Instance ⟨.Virtual 0 3, #[]⟩ }) {}
  check (result.isOk && state.trace.take 2 == ["virtual", "findMir"]) "virtual dispatch"
  let spread := { hooks with
    findMirOrEvalFn := fun _ inst _ _ _ _ _ => log "findMir" (some (loaded ⟨1, by decide⟩, inst)) }
  let (state, result) := Call.run (Call.initFnCall spread () 4 request) {}
  check (result.isOk && state.trace.contains "tupleFields") "spread argument"
  let closure := { hooks with
    nonCapturingClosure := fun _ _ _ => log "nonCapturing" true }
  let (state, result) := Call.run (Call.initFnCall closure () 4 request) {}
  check (result.isOk && !state.trace.contains "copy" && state.trace.contains "storageLive") "noncapturing closure self"
  let variadicAbi : TestAbi := ⟨#[layout], layout, true, true, 0⟩
  let variadic := { hooks with
    fnAbiOfInstance := fun _ _ _ => log "fnAbi" variadicAbi
    allocateStack := fun _ _ => log "allocateStack" mplace
    copyToMemory := fun _ _ _ => log "copyToMemory" ()
    vaListPtr := fun _ _ => log "vaListPtr" ⟨Size.ZERO, some ()⟩
    writeZeroBytes := fun _ _ _ => log "writeZeroBytes" ()
    vaListKeyField := fun _ _ => log "vaListKeyField" mplace
    writePointerToMemory := fun _ _ _ => log "writePointerToMemory" () }
  let (state, result) := Call.run (Call.initFnCall variadic () 4 { request with callerFnAbi := some variadicAbi }) {}
  check (result.isOk && state.frame.vaList.size == 1 && state.trace.contains "writePointerToMemory") "varargs initialize and ownership"
  let tailFrame := { frame with returnContinuation := .goto (some 7) .Continue }
  let evaluated : EvaluatedCall Unit Unit Bool TestAbi := ⟨request.callee, request.args, false,
    request.callerFnAbi, false⟩
  let (state, result) := Call.run (Call.initFnTailCall hooks () 4 evaluated) { frame := tailFrame, index := 1 }
  check (result.isOk && state.index == 1 && state.trace.head? == some "popRaw" &&
    state.trace.getLast? == some "cleanup" && !state.trace.contains "protect") "tail call copies args before pop, cleanup after init"
  let dropped := { hooks with
    isDynamic := fun _ => log "isDynamic" true
    unpackDynForDrop := fun _ p => log "unpackDyn" p
    resolveDropGlue := fun _ _ => log "resolveDrop" ⟨.Shim (.DropGlue 0 (some 0)), #[]⟩
    mplaceToMutRef := fun _ _ => log "mutRef" op
    fakeUnitReturn := fun _ => log "fakeUnit" runtimePlace }
  let (state, result) := Call.run (Call.initDropInPlaceCall dropped () 4 runtimePlace ⟨.Virtual 0 0, #[]⟩ 1 .Continue) {}
  check (result.isOk && state.trace.take 7 == ["forceAllocation", "isDynamic", "unpackDyn", "resolveDrop", "fnAbi", "mutRef", "fakeUnit"]) "dynamic drop resolution"
  let trackMismatch := { hooks with requiresCallerLocation := fun _ => log "requiresLocation" true }
  let (state, result) := Call.run (Call.initFnCall trackMismatch () 4 request) {}
  check (!result.isOk && state.index == 0 && state.trace == ["findMir", "requiresLocation"]) "track caller mismatch before frame push"
  let conventionMismatch := { hooks with sameConvention := fun _ _ => false }
  let (state, result) := Call.run (Call.initFnCall conventionMismatch () 4 request) {}
  check (!result.isOk && state.index == 0 && !state.trace.contains "targetFeatures") "convention mismatch before features and push"
  let failFeatures := { hooks with checkTargetFeatures := fun _ _ => blocked "targetFeatures" }
  let (state, result) := Call.run (Call.initFnCall failFeatures () 4 request) {}
  check (!result.isOk && state.index == 0 && state.trace.getLast? == some "targetFeatures") "feature failure before destination read and push"
  let (state, result) := Call.run (Call.initFnCall foreign () 1
    { request with callee := .Other (), callerFnAbi := none }) {}
  check (!result.isOk && state.trace.isEmpty) "foreign call requires ABI"
  let failedVarargs := { variadic with checkArgumentCompat := fun _ _ _ => do
    let s ← get
    log "compat" (!s.trace.contains "copyToMemory") }
  let (state, result) := Call.run (Call.allocateVarargs failedVarargs ()
    #[(.Copy op, layout), (.Copy op, layout)] #[layout, layout]) {}
  check (!result.isOk && state.trace == ["compat", "allocateStack", "copyToMemory", "compat"]) "varargs partial allocation remains on later error"
