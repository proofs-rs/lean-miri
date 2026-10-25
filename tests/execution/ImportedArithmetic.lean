import Miri.Input.CallResolution
import tests.execution.ReturnMemory
import Miri.Input.RuntimeMetadata
import Miri.Input.Decoder
import Miri.Input.LowerMIR
import Miri.Interpreter.ScalarOps
import Miri.Interpreter.ControlFlow
import Miri.Interpreter.LocalAccess

open Miri Miri.ABI Miri.Memory Miri.Interpreter

/-! Executes the compiler-exported add_one body. Compiler metadata comes from the internal canonical bridge. Execution is
restricted to this fixture's integer/bool/tuple immediate-local path; all other
operations fail explicitly. No replacement MIR body is constructed. -/
private def Option.toExcept (value : Option A) (error : E) : Except E A :=
  match value with | some value => .ok value | none => .error error
private abbrev Result := Except String
private def need (value : Option A) (name : String) : Result A :=
  value.toExcept s!"missing {name}"
private abbrev Metadata := Input.RuntimeMetadata
private def metadataError (e : Input.RuntimeMetadataError) : StepError := .invalidProgram (toString e)
private def lookup (m : Metadata) (ty : MIR.TyId) := (m.lookup ty).mapError metadataError
private def node (m : Metadata) (ty : MIR.TyId) := (m.node ty).mapError metadataError
private def findKind (m : Metadata) (kind : Input.TypeShapeKind) := (m.findKind kind).mapError metadataError
private def fieldType (m : Metadata) (parent : TyAndLayout MIR.TyId) (index : Nat) := (m.field parent index).mapError metadataError

private structure Machine where
  returnMemory : ReturnMemory.State
  returnPlace : MemoryOperandPlace AllocId
  returned : Bool := false
  trace : List String := []
private abbrev State := StepState AllocId (TyAndLayout MIR.TyId) Unit Machine
private abbrev Exec := RvalueM State
private def lift (value : Except StepError A) : Exec A :=
  match value with | .ok value => pure value | .error e => throw e
private def event (name : String) : Exec Unit :=
  modify fun s => { s with machine.trace := s.machine.trace ++ [name] }
private def current : Exec (Frame AllocId (TyAndLayout MIR.TyId) Unit) := do
  lift ((← get).stack.currentFrame?.toExcept (.stack .emptyStack))
private def putFrame (frame : Frame AllocId (TyAndLayout MIR.TyId) Unit) : Exec Unit :=
  modify fun s => { s with stack.frames := s.stack.frames.pop.push frame }
private def block (name : String) : Exec A := throw (.unsupported name)
private def localLayout (m : Metadata) (localId : MIR.LocalId) : Exec (TyAndLayout MIR.TyId) := do
  let frame ← current
  let decl ← lift ((frame.body.locals[localId]?).toExcept (.stack (.invalidLocal localId frame.locals.size)))
  lift (lookup m decl)

private def validateImmediate (value : Immediate AllocId) (layout : LayoutData) : Except ProjectionError Unit := do
  let check (scalar : Memory.Scalar AllocId) (abi : ABI.Scalar) : Except ProjectionError Unit := do
    let integer ← scalar.toScalarInt.mapError (fun e => .invariant (toString e))
    let bits ← integer.toBits (match abi.primitive with | .Int i _ => i.size | _ => Size.ZERO)
      |>.mapError (fun e => .invariant (toString e))
    match abi with
    | .Initialized (validRange := range) =>
        if !range.contains bits then throw (.invariant "invalid scalar range")
    | .Union => pure ()
  match value, layout.backendRepr with
  | .scalar value, .Scalar abi => check value abi
  | .scalarPair a b, .ScalarPair (a := aa) (b := bb) => check a aa; check b bb
  | .uninit, _ => throw (.invariant "uninitialized value")
  | _, _ => throw (.invariant "immediate ABI mismatch")

private def projection (m : Metadata) : ProjectionCx AllocId := {
  -- Guarded x86_64 target below: PointerArithmetic::max_size_of_val uses
  -- isize::MAX. This fixture exercises tuple fields, never index arithmetic.
  target := m.target.base, maxSizeOfVal := Size.ofBytes 9223372036854775807
  isSliceOrStr := fun _ => .ok false
  field := fun parent index => (fieldType m parent index).mapError (fun e => .obligation (reprStr e))
  variant := fun _ _ => .error (.obligation "variant")
  dynamicAlign := fun _ _ => .error (.obligation "dynamicAlign")
  packedAlign := fun _ => .error (.obligation "packedAlign")
  immediateOffset := projectionImmediateOffset validateImmediate
  memoryOffset := fun _ _ _ _ => .error (.obligation "memoryOffset")
  subsliceLayout := fun _ _ => .error (.obligation "subsliceLayout")
  layoutOf := fun ty => (lookup m ty).mapError (fun e => .obligation (reprStr e))
  deref := fun _ => .error (.obligation "deref")
  localIndex := fun _ => .error (.obligation "localIndex") }

private def localHooks (m : Metadata) : LocalAccessHooks AllocId Unit (List String) := {
  layout := fun frame state localId known =>
    ⟨frame, state, do
      let ty ← (frame.body.locals[localId]?).toExcept (.resolver "missing local type")
      let layout ← (lookup m ty).mapError (fun e => .resolver (reprStr e))
      if let some known := known then
        if known != layout then throw (.resolver "known layout mismatch")
      pure layout⟩
  validationInProgress := fun _ => false
  afterLocalRead := fun frame state _ => ⟨frame, state ++ ["readLocal"], .ok ()⟩
  project := fun frame state op elem =>
    let result := localProjectionHook (projection m) frame state op elem
    { result with state := result.state ++ ["project"] }
  -- This fixture runs the source's disabled debug MIR-type-sanity policy.
  -- Actual canonical layout and field queries still run independently.
  checkPlaceType := fun frame state _ _ => ⟨frame, state, .ok ()⟩
  runtimeChecks := fun frame state _ => ⟨frame, state, .error (.resolver "runtime checks")⟩
  constant := fun frame state _ _ => ⟨frame, state, .error (.resolver "constant hook unused")⟩ }
private def evalPlaceOp (m : Metadata) (place : MIR.Place) (known : Option (TyAndLayout MIR.TyId)) : Exec (OpTy AllocId) := do
  let frame ← current
  let state ← get
  let result := evalPlaceToOp (localHooks m) frame state.machine.trace place known
  putFrame result.frame
  modify fun s => { s with machine.trace := result.state }
  lift (result.outcome.mapError (fun e => .invalidProgram (reprStr e)))
private def evalOperand (m : Metadata) (operand : MIR.Operand) (known : Option (TyAndLayout MIR.TyId)) : Exec (OpTy AllocId) := do
  match operand with
  | .Copy place | .Move place => evalPlaceOp m place known
  | .Constant constant =>
    match constant.value with
    | .Val (.Scalar (.Int bits bytes)) ty =>
      let layout ← lift (lookup m ty)
      if layout.layout.size.bytes.toNat != bytes then throw (.invalidProgram "constant width")
      if let some known := known then
        if known != layout then throw (.invalidProgram "constant known layout")
      let integer ← lift ((ScalarInt.tryFromUInt (BitVec.ofNat 128 bits) layout.layout.size).mapError (fun e => .invalidProgram (toString e)))
      let integer ← lift (integer.toExcept (.invalidProgram "constant overflow"))
      event "constant"
      return ⟨.immediate (.scalar (.fromScalarInt integer)), layout⟩
    | _ => block "unsupported constant"
  | .RuntimeChecks _ => block "runtime checks"
private def readImmediate (op : OpTy AllocId) : Exec (RvalueImmTy AllocId) := do
  let .immediate value := op.op | block "indirect immediate read"
  lift ((validateImmediate value op.layout.layout).mapError (fun e => .invalidProgram (reprStr e)))
  return ⟨value, op.layout⟩
private structure Dest where
  localId : MIR.LocalId
  layout : TyAndLayout MIR.TyId
private def evalDest (m : Metadata) (place : MIR.Place) (_skip : Bool) : Exec Dest := do
  if !place.projection.isEmpty then block "projected write"
  return ⟨place.localId, ← localLayout m place.localId⟩
private def writeLocal (dest : Dest) (value : Immediate AllocId) : Exec Unit := do
  let frame ← current
  let hooks : LocalWriteHooks AllocId Unit Unit := {
    validationInProgress := fun _ => false
    afterLocalWrite := fun frame state _ => ⟨frame, state, .ok ()⟩
    checkImmediateAbi := fun frame state value layout =>
      ⟨frame, state, (validateImmediate value layout.layout).mapError .projection⟩ }
  let result := writeImmediateLocalBranch hooks frame () dest.localId dest.layout value
  putFrame result.frame
  event "writeLocal"
  lift (result.outcome.mapError (fun e => .invalidProgram (reprStr e)))

private def scalarHooks (m : Metadata) : ScalarOpsHooks AllocId State Unit := {
  classify := fun _ ty => do
    let node ← lift (node m ty)
    match node.shapeKind with
    | .bool => pure .boolean
    | .uint =>
      match node.shapeMetadata.unsignedKind with
      | some (.known kind) => pure (.integer kind)
      | _ => block "integer kind"
    | _ => block "type classification"
  boolLayout := fun _ => lift (findKind m .bool)
  orderingLayout := fun _ => block "ordering layout"
  overflowLayout := fun _ left => do
    let tuple ← lift ((m.overflowTupleLayout left).mapError metadataError)
    let first ← lift (fieldType m tuple 0)
    let second ← lift (fieldType m tuple 1)
    let boolean ← lift (findKind m .bool)
    if first != left || second != boolean then throw (.invalidProgram "overflow tuple metadata")
    pure tuple
  metadataLayout := fun _ _ => block "metadata layout"
  unitLayout := fun _ => block "unit layout"
  floatBinary := fun _ _ _ _ => block "float binary"
  pointerBinary := fun _ _ _ _ => block "pointer binary"
  floatUnary := fun _ _ _ => block "float unary"
  derefValidity := fun _ _ => block "deref validity" }

private def rvalueHooks (m : Metadata) : RvalueHooks AllocId State Unit Dest := {
  placeLayout := Dest.layout
  evalPlace := fun _ place skip => evalDest m place skip
  evalOperand := fun _ => evalOperand m
  evalPlaceToOp := fun _ => evalPlaceOp m
  readImmediate := fun _ => readImmediate
  writeImmediate := fun _ value dest => writeLocal dest value
  writePointer := fun _ _ _ => block "pointer write"
  threadLocalPointer := fun _ _ => block "thread localId"
  withRetagMode := fun _ mode action => do
    -- Fixture layouts contain only integer/bool scalars. A mode change has no
    -- pointer to visit, and the scoped action is still run in source order.
    event s!"retag:{reprStr mode}"
    action
  copyOp := fun _ op dest => do
    if op.layout != dest.layout then throw (.invalidProgram "copy layout")
    let value ← readImmediate op
    writeLocal dest value.imm
  copyOpAllowTransmute := fun _ _ _ => block "transmute copy"
  binaryOp := fun c op left right => do
    event "scalarBinary"
    ScalarOps.binary (scalarHooks m) c op left right
  unaryOp := ScalarOps.unary (scalarHooks m)
  writeAggregate := fun _ _ _ _ => block "aggregate"
  writeRepeat := fun _ _ _ => block "repeat"
  forceAllocation := fun _ _ => block "force allocation"
  toRef := fun _ _ => block "toRef"
  enforceValidity := fun _ _ => block "enforceValidity reference"
  retagPtrValue := fun _ _ _ => block "retag pointer"
  placeBaseRaw := fun _ _ => block "raw base"
  normalize := fun _ _ => block "normalize"
  cast := fun _ _ _ _ _ => block "cast"
  readDiscriminant := fun _ _ => block "discriminant"
  discriminantForVariant := fun _ _ _ => block "discriminant value" }

private def storageHooks (m : Metadata) : LocalStorageHooks AllocId (TyAndLayout MIR.TyId) Unit Unit := {
  veryTriviallySized := fun ty => do
    let node ← (node m ty).mapError (fun e => .layoutFailure (reprStr e))
    match node.shapeKind with
    | .uint | .bool => pure true
    | .tuple => pure false
    | _ => throw (.unsupportedUnexpectedLocalType 0 ty)
  layout := fun state frame localId => ⟨state, do
    let ty ← (frame.body.locals[localId]?).toExcept (.missingLocalType localId)
    (lookup m ty).mapError (fun e => .layoutFailure (reprStr e))⟩
  isSized := fun layout => layout.layout.isSized
  afterLocalWrite := fun state _ _ => ⟨state, .ok ()⟩
  allocateDyn := fun state _ _ => ⟨state, .error (.allocationFailure "unsupported dynamic allocation")⟩
  deallocateStack := fun state _ => ⟨state, .error (.deallocationFailure "unsupported deallocation")⟩ }
private def storage (m : Metadata) (localId : MIR.LocalId) (live : Bool) : Exec Unit := do
  let frame ← current
  let result := if live then frame.storageLive () (storageHooks m) localId
    else frame.storageDead () (storageHooks m) localId
  putFrame result.frame
  lift (result.outcome.mapError StepError.stack)
  event (if live then "storageLive" else "storageDead")
private def readBool (m : Metadata) (operand : MIR.Operand) : Exec Bool := do
  event "assertCondition"
  let value ← readImmediate (← evalOperand m operand none)
  let scalar ← lift (value.imm.toScalar.mapError (fun e => .invalidProgram (reprStr e)))
  lift (scalar.toBool.mapError ScalarOps.scalarError)

private def controlHooks (m : Metadata) : TerminatorHooks AllocId (TyAndLayout MIR.TyId) Unit Machine Unit (OpTy AllocId) (RvalueImmTy AllocId) := {
  bodySpan := fun _ => .error (.unsupported "unwind body span query")
  returnOperand := fun _ state => runRvalue (evalPlaceOp m ⟨0, #[]⟩ none) state
  popFrame := fun _ state =>
    match state.stack.popFrame with
    | .error e => (state, .error (.stack e))
    | .ok (stack, frame) => ({ state with stack }, .ok frame)
  copyReturn := fun _ op destination state =>
    match destination, op.op with
    | .memory place, .immediate value =>
      if place.layout != op.layout then
        (state, .error (.invalidProgram "return layout mismatch"))
      else
        let (memory, outcome) := ReturnMemory.write m.target.base state.machine.returnMemory ⟨place.mplace,localMemoryLayout place.layout⟩ value
        ({ state with machine := { state.machine with
            returnMemory := memory
            returned := outcome.isOk
            trace := state.machine.trace ++ ["returnMemoryWrite"] } }, outcome)
    | _, _ => (state, .error (.unsupported "non-memory return destination or indirect source"))
  cleanupFrame := fun _ unwinding frame state =>
    if unwinding then (state, .error (.unsupported "unwind cleanup"))
    else if frame.locals.any (fun localState => match localState.value with
      | .live (.indirect _) => true | _ => false) then
      (state, .error (.unsupported "memory cleanup"))
    else ({ state with machine.trace := state.machine.trace ++ ["cleanup"] }, .ok .normal)
  unwindTerminate := fun _ _ state => (state, .error (.unsupported "unwind terminate"))
  evalDiscriminant := fun _ _ state => (state, .error (.unsupported "switch discriminant"))
  compareSwitchCase := fun _ _ _ state => (state, .error (.unsupported "switch comparison"))
  call := fun _ _ state => (state, .error (.unsupported "call"))
  tailCall := fun _ _ state => (state, .error (.unsupported "tail call"))
  drop := fun _ _ _ _ state => (state, .error (.unsupported "drop"))
  ignoreOptionalOverflowChecks := fun _ => false
  readAssertCondition := fun _ operand state => runRvalue (readBool m operand) state
  assertPanic := fun _ _ _ state =>
    ({ state with machine.trace := state.machine.trace ++ ["assertPanic"] }, .error (.machineStop "assertion panic")) }
private def stepHooks (m : Metadata) : StepHooks AllocId (TyAndLayout MIR.TyId) Unit Machine Unit Dest := {
  assign := fun _ place value state => runRvalue (evalRvalueIntoPlace (rvalueHooks m) () value place) state
  evalPlace := fun _ place skip state => runRvalue (evalDest m place skip) state
  writeDiscriminant := fun _ _ _ state => (state, .error (.unsupported "write discriminant"))
  storageLive := fun _ localId state => runRvalue (storage m localId true) state
  storageDead := fun _ localId state => runRvalue (storage m localId false) state
  intrinsic := fun _ _ state => (state, .error (.unsupported "intrinsic"))
  incrementConstEvalCounter := fun _ state => (state, .error (.unsupported "const eval counter"))
  returnFromCurrentFrame := fun _ unwind => ControlFlow.returnFromCurrentFrame (controlHooks m).toControlHooks () unwind
  beforeTerminator := fun _ state => (state, .ok ())
  terminator := fun _ term => ControlFlow.evalTerminator (controlHooks m) () term }

private def execute (m : Metadata) (fuel : Nat) (state : State) : State × Except StepError Unit :=
  match fuel with
  | 0 => (state, .error (.resourceExhaustion "test fuel"))
  | fuel+1 =>
    let (state,result) := Step.step (stepHooks m) () state
    match result with
    | .error e => (state, .error e)
    | .ok false => (state, .ok ())
    | .ok true => execute m fuel state
private def initialState (m : Metadata) (lowered : Input.LoweredBody) (loaded : LoadedBody) (argument : Nat) : Result State := do
  if lowered.body.argumentCount != 1 then throw "expected one argument"
  let retTy ← need lowered.body.locals[0]? "return type"
  let retLayout ← (lookup m retTy).mapError reprStr
  let span ← need lowered.spans[0]? "source span"
  let _ := span
  let (returnMemory, output) ← (ReturnMemory.create m.target.base retLayout).mapError reprStr
  let returnPlace : RuntimeStackPlace AllocId := .memory ⟨output.mplace,retLayout⟩
  let definition ← lowered.ownDefinitionId
  let (_,localsIdentity) := (LocalsIdentitySupply.mk 0).allocate
  let frame : Frame AllocId (TyAndLayout MIR.TyId) Unit :=
    Frame.create loaded ⟨.Item definition, #[]⟩ () (.stop true) returnPlace ⟨0⟩ localsIdentity
  let mut frame := { frame with location := .mir ⟨0,0⟩ }
  -- MIR locals without StorageLive are always live; source liveness analysis
  -- determines this set from the imported statements.
  let scheduled := lowered.body.basicBlocks.foldl (fun locals block =>
    block.statements.foldl (fun locals stmt => match stmt.kind with
      | .StorageLive localId => locals.push localId | _ => locals) locals) (#[] : Array Nat)
  for localId in List.range frame.locals.size do
    if !scheduled.contains localId then
      let result := frame.storageLive () (storageHooks m) localId
      frame ← result.outcome.mapError toString *> pure result.frame
  let argTy ← need lowered.body.locals[1]? "argument type"
  let argLayout ← (lookup m argTy).mapError reprStr
  let integer ← (ScalarInt.tryFromUInt (BitVec.ofNat 128 argument) argLayout.layout.size).mapError toString
  let integer ← need integer "argument fit"
  frame ← (frame.setLocalOperand 1 (.immediate (.scalar (.fromScalarInt integer)))).mapError toString
  pure ⟨⟨#[frame]⟩, { returnMemory, returnPlace := output }⟩
private def must (result : Except String A) : IO A :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)
private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def main (args : List String) : IO Unit := do
  let path ← match args with
    | path::_ => pure path
    | [] => throw (IO.userError "usage: ImportedArithmetic <selected add_one export>")
  let decoded ← must (Input.decodeJson (← IO.FS.readFile path))
  check (decoded.document.producer.targetTriple == "x86_64-unknown-linux-gnu") "unsupported fixture target"
  let program ← must (Input.lowerProgram decoded.document)
  let prepared ← must (Input.CallResolution.prepare program)
  let definition ← must (prepared.program.rootDefinitionId 0)
  let loaded ← must (Input.CallResolution.loadedBodyOfInstance prepared ⟨.Item definition,#[]⟩)
  let lowered ← must (need prepared.program.bundle.bodies[loaded.identity.index]? "canonical root instance body")
  let metadata := prepared.runtime
  check (metadata.obligations.isEmpty) "fixture layout import obligations"
  check (metadata.target.base == TargetDataLayout.mk .little .w64) "exported target mismatch"
  let initial ← must (initialState metadata lowered loaded 41)
  let (_, beforeWrite) := ReturnMemory.read metadata.target.base initial.machine.returnMemory initial.machine.returnPlace
  check (!beforeWrite.isOk) "uninitialized return memory read succeeded"
  let (finished,outcome) := execute metadata 100 initial
  check outcome.isOk s!"execution failed: {reprStr outcome}"
  check finished.stack.frames.isEmpty "Return did not pop root frame"
  check finished.machine.returned "Return did not copy into memory"
  let (readMemory, readResult) := ReturnMemory.read metadata.target.base finished.machine.returnMemory finished.machine.returnPlace
  let immediate ← must (readResult.mapError reprStr)
  check (finished.machine.returnMemory.events.contains "write-return" &&
    readMemory.events.contains "read-return" && readMemory.events.contains "resolve-return" &&
    readMemory.events.contains "return-allocation") "return did not traverse allocation access"
  let scalar ← must (immediate.value.toScalar.mapError reprStr)
  let bits ← must (scalar.toBits immediate.layout.size |>.mapError reprStr)
  let returnedLayout ← must (((metadata.integerLayout .u32).mapError metadataError).mapError reprStr)
  check (bits.toNat == 42) "add_one(41) != 42"
  check (finished.machine.trace.contains "scalarBinary" && finished.machine.trace.contains "project" &&
    finished.machine.trace.contains "writeLocal" && finished.machine.trace.contains "assertCondition" &&
    finished.machine.trace.contains "returnMemoryWrite") "integration path missing"
  let overflowInitial ← must (initialState metadata lowered loaded 4294967295)
  let (panicked,overflow) := execute metadata 100 overflowInitial
  check (overflow == Except.error (StepError.machineStop "assertion panic")) "overflow failed to reach Assert panic"
  check (!panicked.machine.returned && panicked.machine.trace.contains "assertPanic") "overflow returned normally"
  let unknown := runRvalue (ScalarOps.binary (scalarHooks metadata) () .Add
    ⟨.uninit, { returnedLayout with ty := 999999 }⟩ ⟨.uninit, returnedLayout⟩) initial
  check (!unknown.2.isOk) "unknown type accepted"
  let missing := { metadata with layouts := #[], layoutCache := none }
  let rejected := execute missing 100 initial
  check (!rejected.2.isOk) "missing layout accepted"
  IO.println "returned=42"
  IO.println "overflow=panic"
  IO.println s!"actual exported add_one: 41 -> 42; overflow -> Assert panic; missing/unknown metadata rejected; {finished.machine.trace.length} recorded operations"
