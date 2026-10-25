import Miri.Input.CallResolution
import tests.execution.GlobalMemory
import Miri.Interpreter.Constant
import Miri.Interpreter.Place
import Miri.Input.RuntimeMetadata
import Miri.Input.Decoder
import Miri.Input.LowerMIR
import Miri.Interpreter.Call
import Miri.Interpreter.ScalarOps
import Miri.Interpreter.ControlFlow
import Miri.Interpreter.LocalAccess

open Miri Miri.ABI Miri.Memory Miri.Interpreter

/-! Executes compiler-exported immutable static reads and nested function calls. Compiler metadata comes from the internal canonical bridge. Execution is
restricted to this fixture's integer/bool/tuple immediate-localRefs path; all other
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
  returnMemory : GlobalMemory.State
  returnPlace : MemoryOperandPlace CtfeProvenance
  localsSupply : LocalsIdentitySupply := ⟨0⟩
  returned : Bool := false
  trace : List String := []
private abbrev State := StepState CtfeProvenance (TyAndLayout MIR.TyId) Nat Machine
private abbrev Exec := RvalueM State
private def lift (value : Except StepError A) : Exec A :=
  match value with | .ok value => pure value | .error e => throw e
private def event (name : String) : Exec Unit :=
  modify fun s => { s with machine.trace := s.machine.trace ++ [name] }
private def current : Exec (Frame CtfeProvenance (TyAndLayout MIR.TyId) Nat) := do
  lift ((← get).stack.currentFrame?.toExcept (.stack .emptyStack))
private def putFrame (frame : Frame CtfeProvenance (TyAndLayout MIR.TyId) Nat) : Exec Unit :=
  modify fun s => { s with stack.frames := s.stack.frames.pop.push frame }
private def block (name : String) : Exec A := throw (.unsupported name)
private def localLayout (m : Metadata) (localId : MIR.LocalId) : Exec (TyAndLayout MIR.TyId) := do
  let frame ← current
  let decl ← lift ((frame.body.locals[localId]?).toExcept (.stack (.invalidLocal localId frame.locals.size)))
  lift (lookup m decl)

private def validateImmediate (value : Immediate CtfeProvenance) (layout : LayoutData) : Except ProjectionError Unit := do
  let check (scalar : Memory.Scalar CtfeProvenance) (abi : ABI.Scalar) : Except ProjectionError Unit := do
    if let .Pointer _ := abi.primitive then
      if !scalar.isPointer || scalar.size != Size.ofBytes 8 then throw (.invariant "invalid reference pointer representation")
      return ()
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

private def projection (m : Metadata) : ProjectionCx CtfeProvenance := {
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

private def localHooks (m : Metadata) : LocalAccessHooks CtfeProvenance Nat (List String) := {
  layout := fun frame state localId known =>
    ⟨frame, state, do
      let ty ← (frame.body.locals[localId]?).toExcept (.resolver "missing localRefs type")
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
private def readLocal (m : Metadata) (localId : MIR.LocalId) : Exec (OpTy CtfeProvenance) := do
  let frame ← current
  let state ← get
  let result := localToOp (localHooks m) frame state.machine.trace localId none
  putFrame result.frame
  modify fun s => { s with machine.trace := result.state }
  lift (result.outcome.mapError (fun e => .invalidProgram (reprStr e)))
private def validateMemory (m : Metadata) (place : MemoryOperandPlace CtfeProvenance) : Exec Unit := do
  let state ← get
  let (memory,result) := GlobalMemory.validate m.target state.machine.returnMemory place
  set { state with machine.returnMemory := memory }
  lift result
private def pointerPlace (m : Metadata) (op : OpTy CtfeProvenance) : Exec (RuntimePlace CtfeProvenance) := do
  let node ← lift (node m op.layout.ty)
  if node.shapeKind != .reference then block "non-reference dereference"
  let .immediate value := op.op | block "indirect reference operand"
  let scalar ← lift (value.toScalar.mapError (fun e => .invalidProgram (reprStr e)))
  let ptr ← lift (scalar.toPointer m.target.base |>.mapError (fun e => .invalidProgram (reprStr e)))
  let pointee ← lift ((m.pointee op.layout).mapError metadataError)
  if !pointee.layout.isSized then block "unsized reference"
  return ⟨.memory ⟨ptr,.none,none⟩,pointee⟩
private def placeHooks (m : Metadata) : PlaceHooks CtfeProvenance State Unit Nat := {
  debugAssertions := false
  getFrame := current, setFrame := putFrame
  frameIndex := do lift ((← get).stack.frameIndex.mapError StepError.stack)
  resolveLayout := fun _ => localLayout m
  localToOp := fun _ => readLocal m
  projection := fun _ => pure (projection m)
  deref := fun _ place skip => do
    let op ← match place.ref with
      | .local frame localId none identity =>
        let actual ← current
        if actual.localsIdentity != identity then block "stale dereference locals identity"
        if frame + 1 != (← get).stack.frames.size then block "deref of another frame"
        readLocal m localId
      | _ => block "nested memory/projected reference deref"
    let result ← pointerPlace m op
    if !skip then
      let .memory memory := result.ref | block "reference result"
      validateMemory m ⟨memory,localMemoryLayout result.layout⟩
    event "placeDeref"
    return result
  checkPlaceType := fun _ _ _ => pure () -- Source debug type sanity disabled.
  allocateStack := fun _ _ => block "place force allocation"
  writeMemoryNoValidate := fun _ _ _ => block "place write unused"
  afterLocalMovedToMemory := fun _ _ _ => block "place migration"
  memoryOffset := fun _ _ _ _ _ => block "place memory offset"
  writeLocalImmediate := fun _ _ _ _ => block "place local write unused"
  enforceValidity := fun _ _ => pure true
  validate := fun _ _ => block "place whole-value validation unused" }
private def evalPlaceOp (m : Metadata) (place : MIR.Place) (known : Option LocalLayout) : Exec (OpTy CtfeProvenance) := do
  let result ← Miri.Interpreter.evalPlace (placeHooks m) () place false
  let op ← Miri.Interpreter.placeToOp (placeHooks m) () result
  if let some known := known then
    if known != op.layout then throw (.invalidProgram "known place layout")
  return op
private def constantQueries : ConstantQueries CtfeProvenance Unit Unit (Array String) := {
  instantiateAndNormalize := fun fnInstance constant => do
    if !fnInstance.args.isEmpty then throw (.query "generic constant normalization unavailable")
    match constant with
    | .Val .. => pure constant
    | _ => throw (.query "non-value normalization evidence unavailable")
  evaluate := fun _ _ _ => throw (.query "compiler constant query unavailable")
  adjustGlobalRootPointer := fun pointer => do
    modify fun state => { state with hooks := state.hooks.push "constant-root" }
    pure pointer
  externStaticPointer := fun _ => throw (.query "extern static pointer unavailable") }
private def evalOperand (m : Metadata) (operand : MIR.Operand) (known : Option LocalLayout) : Exec (OpTy CtfeProvenance) := do
  match operand with
  | .Copy place | .Move place => evalPlaceOp m place known
  | .Constant constant =>
    let frame ← current
    let state ← get
    let view := ConstantState.fromFrame state.machine.returnMemory.memory state.machine.returnMemory.events frame
    let result := evalConstOperand m constantQueries constant view
    let (after,outcome) := match result with
      | .ok value state => (state,Except.ok value)
      | .error error state => (state,Except.error (StepError.invalidProgram (reprStr error)))
    set { state with machine := { state.machine with returnMemory :=
      { state.machine.returnMemory with memory := after.memory, events := after.hooks } } }
    let op ← lift outcome
    if let some known := known then
      if known != op.layout then throw (StepError.invalidProgram "constant known layout")
    event "evalConstant"
    return op
  | .RuntimeChecks _ => block "runtime checks"
private def readImmediate (m : Metadata) (op : OpTy CtfeProvenance) : Exec (RvalueImmTy CtfeProvenance) := do
  match op.op with
  | .immediate value =>
    lift ((validateImmediate value op.layout.layout).mapError (fun e => .invalidProgram (reprStr e)))
    return ⟨value,op.layout⟩
  | .indirect _ =>
    let state ← get
    let context := GlobalMemory.context m.target state.machine.returnMemory.image
    let result ← placeReadRaw context
      (fun state : State => state.machine.returnMemory.memory)
      (fun state : State => state.machine.returnMemory.events)
      (fun state memory events => { state with machine.returnMemory := { state.machine.returnMemory with memory,events } })
      (fun state touched => { state with machine.trace := state.machine.trace ++
        [if touched.isSome then "memoryTouched" else "memoryUntouched"] }) op
    match result with
    | .place _ => block "non-immediate memory read"
    | .immediate value =>
      lift ((validateImmediate value.value op.layout.layout).mapError (fun e => .invalidProgram (reprStr e)))
      event "placeReadRaw"
      return ⟨value.value,op.layout⟩
private structure Dest where
  localId : MIR.LocalId
  layout : TyAndLayout MIR.TyId
private def evalDest (m : Metadata) (place : MIR.Place) (_skip : Bool) : Exec Dest := do
  if !place.projection.isEmpty then block "projected write"
  return ⟨place.localId, ← localLayout m place.localId⟩
private def writeLocal (m : Metadata) (dest : Dest) (value : Immediate CtfeProvenance) : Exec Unit := do
  let frame ← current
  let hooks : LocalWriteHooks CtfeProvenance Nat Unit := {
    validationInProgress := fun _ => false
    afterLocalWrite := fun frame state _ => ⟨frame, state, .ok ()⟩
    checkImmediateAbi := fun frame state value layout =>
      ⟨frame, state, (validateImmediate value layout.layout).mapError .projection⟩ }
  let result := writeImmediateLocalBranch hooks frame () dest.localId dest.layout value
  putFrame result.frame
  event "writeLocal"
  lift (result.outcome.mapError (fun e => .invalidProgram (reprStr e)))
  let source ← lift (node m dest.layout.ty)
  if source.shapeKind == .reference then
    let reference ← pointerPlace m ⟨.immediate value,dest.layout⟩
    let .memory place := reference.ref | block "reference validity result"
    validateMemory m ⟨place,localMemoryLayout reference.layout⟩

private def scalarHooks (m : Metadata) : ScalarOpsHooks CtfeProvenance State Unit := {
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

private def rvalueHooks (m : Metadata) : RvalueHooks CtfeProvenance State Unit Dest := {
  placeLayout := Dest.layout
  evalPlace := fun _ place skip => evalDest m place skip
  evalOperand := fun _ => evalOperand m
  evalPlaceToOp := fun _ => evalPlaceOp m
  readImmediate := fun _ => readImmediate m
  writeImmediate := fun _ value dest => writeLocal m dest value
  writePointer := fun _ _ _ => block "pointer write"
  threadLocalPointer := fun _ _ => block "thread localId"
  withRetagMode := fun _ mode action => do
    -- Fixture layouts contain only integer/bool scalars. A mode change has no
    -- pointer to visit, and the scoped action is still run in source order.
    event s!"retag:{reprStr mode}"
    action
  copyOp := fun _ op dest => do
    if op.layout != dest.layout then throw (.invalidProgram "copy layout")
    let value ← readImmediate m op
    writeLocal m dest value.imm
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

/-- Restricted execution of pinned stack.rs's recursive type-kind classifier. -/
private def triviallySized (m : Metadata) : Nat → MIR.TyId → Except StackError Bool
  | 0,_ => .error (.layoutFailure "type-classifier recursion exhausted")
  | fuel+1,ty => do
    let value ← (node m ty).mapError (fun e => .layoutFailure (reprStr e))
    match value.shapeKind with
    | .uint | .bool | .never | .functionDefinition | .reference => pure true
    | .tuple =>
      let shape ← Input.RuntimeMetadata.jsonField value.payload "shape" |>.mapError (fun e => .layoutFailure (toString e))
      let elements ← Input.RuntimeMetadata.array shape "elements" |>.mapError (fun e => .layoutFailure (toString e))
      match elements.back? with
      | none => pure true
      | some last =>
        let id ← Input.RuntimeMetadata.number last "type_id" |>.mapError (fun e => .layoutFailure (toString e))
        triviallySized m fuel id
    | _ => throw (.unsupportedUnexpectedLocalType 0 ty)
private def storageHooks (m : Metadata) : LocalStorageHooks CtfeProvenance (TyAndLayout MIR.TyId) Nat Unit := {
  veryTriviallySized := triviallySized m 32
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
  let value ← readImmediate m (← evalOperand m operand none)
  let scalar ← lift (value.imm.toScalar.mapError (fun e => .invalidProgram (reprStr e)))
  lift (scalar.toBool.mapError ScalarOps.scalarError)


private structure ArgABI where
  source : Input.AbiArgument
  layout : LocalLayout
private structure FnABI where
  source : Input.FunctionAbi
  args : Array ArgABI
  ret : ArgABI
private structure Program where
  lowered : Input.LoweredProgram
  metadata : Metadata
  spans : Array Input.SourceSpanData
  bodySpans : Array MIR.SpanRef
  localSpans : Array (Array MIR.SpanRef)
  rustAbi : Input.ExternAbi
  resolution : Input.CallResolution.Prepared

private def compiler (value : Except Input.RuntimeMetadataError A) : Except StepError A :=
  value.mapError metadataError
private def jfield := Input.RuntimeMetadata.jsonField
private def jnat := Input.RuntimeMetadata.number
private def jtext := Input.RuntimeMetadata.text
private def jarray := Input.RuntimeMetadata.array
private def parseSpan (j : Lean.Json) : Except StepError Input.SourceSpanData := do
  let start ← compiler (jfield j "start")
  let stop ← compiler (jfield j "end")
  return {
    originalPayload := j.compress
    lo := ← compiler (jnat j "lo"), hi := ← compiler (jnat j "hi")
    start := ⟨← compiler (jnat start "line"), ← compiler (jnat start "column")⟩
    «end» := ⟨← compiler (jnat stop "line"), ← compiler (jnat stop "column")⟩
    context := ← compiler (jfield j "ctxt" >>= fun p => jtext p "rustc_debug")
    file := ← compiler (jfield j "file" >>= fun p => jtext p "rustc_debug") }
private def internSpan (spans : Array Input.SourceSpanData) (span : Input.SourceSpanData) : Array Input.SourceSpanData × MIR.SpanRef :=
  match spans.toList.idxOf? span with
  | some index => (spans, ⟨index⟩)
  | none => (spans.push span, ⟨spans.size⟩)
private def prepare (document : Input.ImportDocument) : Except StepError Program := do
  let lowered ← (Input.lowerProgram document).mapError StepError.invalidProgram
  let resolution ← (Input.CallResolution.prepare lowered).mapError StepError.invalidProgram
  let lowered := resolution.program
  let metadata := resolution.runtime
  let signature ← (document.types.findSome? (·.signature)).toExcept (.unsupported "Rust signature")
  if signature.abi.kind.tag != "rust" || signature.abi.kind.status != .supported then
    throw (.unsupported "non-Rust ABI fixture")
  let mut spans := lowered.bundle.spans
  let mut bodySpans := #[]
  let mut localSpans := #[]
  for body in lowered.bundle.bodies do
    let span ← parseSpan (← compiler (jfield body.input.payload "span"))
    let (next,bodySpan) := internSpan spans span
    spans := next
    bodySpans := bodySpans.push bodySpan
    let mut localRefs := #[]
    for decl in body.input.locals do
      let (next,ref) := internSpan spans decl.sourceInfo.span
      spans := next
      localRefs := localRefs.push ref
    localSpans := localSpans.push localRefs
  return ⟨lowered, metadata, spans, bodySpans, localSpans, signature.abi, resolution⟩
private def bodyAt (p : Program) (index : Nat) : Except StepError Input.LoweredBody :=
  p.lowered.bundle.bodies[index]?.toExcept (.invalidProgram "body index")
private def sourceDefinition (p : Program) (id : Input.DefinitionId) : Except StepError MIR.DefId :=
  (p.lowered.bundle.definitions.toList.idxOf? id).toExcept (.invalidProgram "definition absent from shared table")
private def genericArgs (j : Lean.Json) : Except StepError (Array MIR.GenericArg) := do
  let args ← j.getArr?.mapError StepError.invalidProgram
  args.mapM fun arg => do
    if (← compiler (jtext arg "kind")) != "type" then throw (.unsupported "non-type generic argument")
    let value ← compiler (jfield arg "value")
    return .Type (← compiler (jnat value "type_id"))
private def currentResolution (p : Program) : Exec Lean.Json := do
  let frame ← current
  if frame.extra != frame.bodyIdentity.index then throw (.invalidProgram "frame source body key mismatch")
  let body ← lift (bodyAt p frame.bodyIdentity.index)
  let .mir location := frame.location | block "call resolution outside MIR"
  let blocks ← lift (compiler (jarray body.input.payload "basic_blocks"))
  let source ← lift (blocks[location.block]?.toExcept (.invalidProgram "source block index"))
  let kind ← lift (compiler (jfield source "terminator" >>= fun term => jfield term "kind"))
  let result ← lift (compiler (jfield kind "resolution"))
  if (← lift (compiler (jtext result "status"))) != "supported" ||
      (← lift (compiler (jtext result "kind"))) != "resolved_instance" then block "unresolved compiler callee"
  return result
private def instanceFromResolution (p : Program) (resolution : Lean.Json) : Except StepError (CallInstance × Input.InstanceId) := do
  let kind ← compiler (jfield resolution "instance_kind")
  if (← compiler (jtext kind "kind")) != "item" then throw (.unsupported "non-Item fnInstance")
  let source ← compiler (jfield kind "def_id")
  let definition : Input.DefinitionId := ⟨← compiler (jnat source "crate"), ← compiler (jnat source "index")⟩
  let id ← sourceDefinition p definition
  let args ← genericArgs (← compiler (jfield resolution "generic_args"))
  let instanceId ← compiler (jnat resolution "instance_id")
  let node ← (p.lowered.input.instances.find? (·.id == instanceId)).toExcept (.invalidProgram "missing fnInstance")
  if node.definitionId != some definition || node.instanceArgsAreMonomorphic != some true then
    throw (.invalidProgram "fnInstance identity or monomorphization mismatch")
  let sourceArgs ← genericArgs (← compiler (jfield node.payload "generic_args"))
  if sourceArgs != args then throw (.invalidProgram "fnInstance generic arguments mismatch")
  return (⟨.Item id, args⟩, instanceId)
private def currentInstance (p : Program) : Exec (CallInstance × Input.InstanceId) := do
  lift (instanceFromResolution p (← currentResolution p))
private def resolvedBody (p : Program) (instanceId : Input.InstanceId) : Except StepError (Nat × Input.LoweredBody) := do
  let (_,index) ← (p.lowered.instances.find? (·.1 == instanceId)).toExcept (.unsupported "fnInstance body unavailable")
  return (index, ← bodyAt p index)
private def resolutionFor (p : Program) (fnInstance : CallInstance) : Except StepError (Lean.Json × Input.InstanceId) := do
  for body in p.lowered.bundle.bodies do
    let blocks ← compiler (jarray body.input.payload "basic_blocks")
    for index in List.range body.body.basicBlocks.size do
      let block ← body.body.basicBlocks[index]?.toExcept (.invalidProgram "block index")
      match block.terminator.kind with
      | .Call .. | .TailCall .. =>
        let block ← blocks[index]?.toExcept (.invalidProgram "source block index")
        let kind ← compiler (jfield block "terminator" >>= fun term => jfield term "kind")
        let resolution ← compiler (jfield kind "resolution")
        let (candidate,id) ← instanceFromResolution p resolution
        if candidate == fnInstance then return (resolution,id)
      | _ => pure ()
  throw (.unsupported "instance has no exported resolution query")
private def getAbi (p : Program) (fnInstance : CallInstance) : Exec FnABI := do
  let (resolution,_) ← lift (resolutionFor p fnInstance)
  let raw ← lift (compiler (jfield resolution "fn_abi"))
  let source ← lift ((p.lowered.input.functionAbis.find? (·.payload == raw)).toExcept (.unsupported "compiler FnABI"))
  if source.callingConvention.status != .supported || source.callingConvention.kind != .rust || source.cVariadic then
    block "unsupported calling convention or varargs"
  let arg (source : Input.AbiArgument) : Except StepError ArgABI := do
    if source.mode.kind != .direct then throw (.unsupported "non-Direct u32 argument ABI")
    let layout ← lookup p.metadata source.typeId
    let node ← node p.metadata source.typeId
    if node.shapeKind != .uint || node.shapeMetadata.unsignedKind != some (.known .u32) then
      throw (.unsupported "non-u32 call ABI")
    return ⟨source, layout⟩
  return ⟨source, ← lift (source.arguments.mapM arg), ← lift (arg source.returnValue)⟩

private def alwaysLive (body : MIR.Body) : Array MIR.LocalId := Id.run do
  let scheduled := body.basicBlocks.foldl (fun locals block =>
    block.statements.foldl (fun locals statement => match statement.kind with
      | .StorageLive id | .StorageDead id => locals.push id | _ => locals) locals) (#[] : Array Nat)
  return (List.range body.locals.size).toArray.filter fun id => id > body.argumentCount && !scheduled.contains id
private def lifecycle (p : Program) (index : Nat) : StackLifecycleHooks CtfeProvenance LocalLayout Nat Machine := {
  freshLocalsIdentity := fun machine =>
    let (supply, identity) := machine.localsSupply.allocate
    ({ machine with localsSupply := supply }, identity)
  storage := {
    veryTriviallySized := (storageHooks p.metadata).veryTriviallySized
    layout := fun machine frame localId =>
      let result := (storageHooks p.metadata).layout () frame localId
      ⟨machine,result.outcome⟩
    isSized := fun layout => layout.layout.isSized
    afterLocalWrite := fun machine _ _ => ⟨{ machine with trace := machine.trace ++ ["storageHook"] }, .ok ()⟩
    allocateDyn := fun machine _ _ => ⟨machine,.error (.allocationFailure "unsized stack allocation")⟩
    deallocateStack := fun machine _ => ⟨machine,.error (.deallocationFailure "indirect localRefs deallocation")⟩ }
  initFrame := fun machine frame =>
    ⟨{ machine with trace := machine.trace ++ ["initFrame"] }, .ok { frame with extra := index }⟩
  requiredConstants := fun stack machine =>
    let result : Except StackError Unit := do
      let body ← (bodyAt p index).mapError (fun e => .machineHookFailure (reprStr e))
      let constants ← compiler (jarray body.input.payload "required_consts") |>.mapError (fun e => .machineHookFailure (reprStr e))
      if !constants.isEmpty then throw (.machineHookFailure "unimplemented required constants")
    ⟨stack,machine,result⟩
  afterPush := fun stack machine => ⟨stack,{ machine with trace := machine.trace ++ ["afterPush"] },.ok ()⟩
  beforePop := fun stack machine => ⟨stack,{ machine with trace := machine.trace ++ ["beforePop"] },.ok ()⟩
  afterPop := fun stack machine _ _ => ⟨stack,{ machine with trace := machine.trace ++ ["afterPop"] },.ok .normal⟩
  alwaysLiveVarsAndTemps := fun body => .ok (alwaysLive body)
  deallocateVararg := fun machine _ => ⟨machine,.error (.deallocationFailure "vararg deallocation")⟩ }
private def pushRaw (p : Program) (fnInstance : CallInstance) (body : LoadedBody) (destination : RuntimeStackPlace CtfeProvenance)
    (continuation : ReturnContinuation) : Exec Unit := do
  let expected ← lift ((Input.CallResolution.loadedBodyOfInstance p.resolution fnInstance).mapError StepError.invalidProgram)
  if expected != body then throw (.invalidProgram "pushed canonical body key does not match compiler instance")
  let index := body.identity.index
  let span ← lift (p.bodySpans[index]?.toExcept (.invalidProgram "preamble source span"))
  let state ← get
  let result := state.stack.pushStackFrameRaw state.machine (lifecycle p index) body fnInstance continuation destination span
  set ({ stack := result.stack, machine := result.state } : State)
  lift (result.outcome.mapError StepError.stack)
private def pushDone (p : Program) : Exec Unit := do
  let frame ← current
  let state ← get
  let result := state.stack.pushStackFrameDone state.machine (lifecycle p frame.extra)
  set ({ stack := result.stack, machine := result.state } : State)
  lift (result.outcome.mapError StepError.stack)
private def popRaw (p : Program) : Exec (Frame CtfeProvenance LocalLayout Nat) := do
  let frame ← current
  let state ← get
  let result := state.stack.popStackFrameRaw state.machine (lifecycle p frame.extra)
  set ({ stack := result.stack, machine := result.state } : State)
  lift (result.outcome.mapError StepError.stack)
private def cleanup (p : Program) (unwinding : Bool) (frame : Frame CtfeProvenance LocalLayout Nat) : Exec ReturnAction := do
  let state ← get
  let result := state.stack.cleanupStackFrame state.machine (lifecycle p frame.extra) unwinding frame
  set ({ stack := result.stack, machine := result.state } : State)
  lift (result.outcome.mapError StepError.stack)
private def runtimePlace (m : Metadata) (place : MIR.Place) (skip : Bool) : Exec (RuntimeStackPlace CtfeProvenance) := do
  let dest ← evalDest m place skip
  let state ← get
  let index ← lift (state.stack.frameIndex.mapError StepError.stack)
  let frame ← current
  return .frameLocal index dest.localId none dest.layout frame.localsIdentity
private def placeToOp (m : Metadata) (place : RuntimeStackPlace CtfeProvenance) : Exec (OpTy CtfeProvenance) := do
  match place with
  | .memory _ => block "memory-backed call destination"
  | .frameLocal frameIndex localId offset expected identity =>
    if offset.isSome then block "offset call destination"
    let state ← get
    let frame ← lift (state.stack.frames[frameIndex]?.toExcept (.stack .emptyStack))
    if frame.localsIdentity != identity then block "stale return-place locals identity"
    let ty ← lift (frame.body.locals[localId]?.toExcept (.stack (.missingLocalType localId)))
    let layout ← lift (lookup m ty)
    if layout != expected then throw (.invalidProgram "runtime place layout")
    return ⟨← lift (frame.getLocalOperand localId |>.mapError StepError.stack),layout⟩
private def copyToRuntime (m : Metadata) (op : OpTy CtfeProvenance) (destination : RuntimeStackPlace CtfeProvenance) : Exec Unit := do
  match destination with
  | .memory place =>
    if op.layout != place.layout then throw (.invalidProgram "return memory layout")
    let value ← readImmediate m op
    let state ← get
    let (memory,result) := GlobalMemory.write m.target state.machine.returnMemory ⟨place.mplace,localMemoryLayout place.layout⟩ value.imm
    set { state with machine := { state.machine with
      returnMemory := memory
      returned := result.isOk
      trace := state.machine.trace ++ ["returnMemoryWrite"] } }
    lift result
  | .frameLocal index localId offset expected identity =>
    if offset.isSome || expected != op.layout then block "projected or incompatible call return"
    let state ← get
    if index + 1 != state.stack.frames.size then block "return destination is not current caller frame"
    let frame ← current
    if frame.localsIdentity != identity then block "stale return-place locals identity"
    let dest ← evalDest m ⟨localId,#[]⟩ false
    if dest.layout != op.layout then throw (.invalidProgram "caller destination type")
    let value ← readImmediate m op
    writeLocal m dest value.imm
    event "callerLocalReturn"

private def callHooks (p : Program) : CallHooks CtfeProvenance State Unit Nat Unit Input.ExternAbi FnABI ArgABI := {
  debugAssertions := false
  getFrame := current
  setFrame := putFrame
  frameIndex := do lift ((← get).stack.frameIndex.mapError StepError.stack)
  evalOperand := fun _ op => evalOperand p.metadata op none
  evalPlace := fun _ => runtimePlace p.metadata
  placeToOp := fun _ => placeToOp p.metadata
  forceAllocation := fun _ _ => block "argument force allocation"
  functionSignature := fun _ layout => do
    let node ← lift (node p.metadata layout.ty)
    let signature ← lift (node.signature.toExcept (.unsupported "function signature"))
    if signature.cVariadic || signature.abi.kind.status != .supported || signature.abi.kind.tag != "rust" then
      block "non-Rust function signature"
    return (signature.inputs.size,signature.abi)
  functionKind := fun ty => do
    let node ← lift (node p.metadata ty)
    if node.shapeKind != .functionDefinition then block "non-FnDef callee"
    let (fnInstance,_) ← currentInstance p
    return .FnDef fnInstance.defId fnInstance.args
  readPointer := fun _ _ => block "function pointer"
  getPtrFn := fun _ _ => block "pointer function resolution"
  resolve := fun _ definition args => do
    let (fnInstance,_) ← currentInstance p
    if fnInstance.defId != definition || fnInstance.args != args then throw (.invalidProgram "resolved identity mismatch")
    event (if args.isEmpty then "resolveItem" else "resolveGeneric")
    pure fnInstance
  fnAbiOfFnPtr := fun _ _ _ => block "function-pointer ABI"
  fnAbiOfInstance := fun _ fnInstance extra => do
    if !extra.isEmpty then block "variadic ABI"
    getAbi p fnInstance
  requiresCallerLocation := fun fnInstance => do
    let abi ← getAbi p fnInstance
    let (_,id) ← lift (resolutionFor p fnInstance)
    let (_,body) ← lift (resolvedBody p id)
    if abi.args.size != body.body.argumentCount then block "implicit caller location or unsupported ABI args"
    pure false
  callerLocation := block "implicit caller location"
  abiCanUnwind := fun abi => abi.source.canUnwind
  abiVariadic := fun abi => abi.source.cVariadic
  abiFixedCount := fun abi => abi.source.fixedCount
  abiArgs := FnABI.args
  abiReturn := FnABI.ret
  sameConvention := fun a b => a.source.callingConvention.payload == b.source.callingConvention.payload
  isRustCall := fun abi => abi.kind.tag == "rust_call"
  rustAbi := p.rustAbi
  argLayout := ArgABI.layout
  argIsIgnore := fun arg => arg.source.mode.kind == .ignore
  isOneZst := fun layout => layout.layout.is1zst
  checkArgumentCompat := fun _ a b => do
    event "argumentCompat"
    -- Restricted source layout_compat: identical u32 types, layout and eq_abi;
    -- ABI mode and every compiler attribute payload must also agree.
    pure (a.layout.ty == b.layout.ty && a.layout.layout == b.layout.layout &&
      a.layout.layout.eqAbi b.layout.layout && a.source.mode.payload == b.source.mode.payload)
  checkTargetFeatures := fun _ fnInstance => do
    let (_,id) ← lift (resolutionFor p fnInstance)
    let node ← lift ((p.lowered.input.instances.find? (·.id == id)).toExcept (.unsupported "source fnInstance"))
    let definition ← lift (node.definitionId.toExcept (.unsupported "fnInstance definition"))
    if definition.crateIndex != 0 || fnInstance.kind != .Item fnInstance.defId then block "non-fixture target features"
    event "fixtureNoTargetFeatures"
  tupleFields := fun _ => block "tuple ABI spreading"
  projectFnArg := fun _ _ _ => block "RustCall spread"
  localLayout := fun _ => localLayout p.metadata
  localSpan := fun body localId => do
    let frame ← current
    if frame.body != body then throw (.invalidProgram "localRefs span body mismatch")
    let refs ← lift (p.localSpans[frame.extra]?.toExcept (.unsupported "source localRefs spans"))
    lift (refs[localId]?.toExcept (.unsupported "source localRefs span"))
  storageLiveDyn := fun _ localId metadata => do
    if metadata.hasMeta then block "argument dynamic metadata"
    storage p.metadata localId true
  copyAllowTransmute := fun _ => copyToRuntime p.metadata
  protectArgument := fun _ _ => block "InPlace protection needs uninitialization"
  withRetagMode := fun _ mode action => do
    event s!"mode:{reprStr mode}"
    let result ← action
    event "restoreMode"
    pure result
  nonCapturingClosure := fun _ fnInstance abi => do
    match fnInstance.kind with
    | .Item _ => pure ()
    | _ => block "closure or shim entry policy"
    if abi.args.size != 1 || abi.args.any (fun arg => arg.layout.layout.is1zst) then
      block "unsupported closure-self ABI"
    -- Every accepted argument ABI was already checked as canonical u32;
    -- a noncapturing closure's special zero-sized self is absent.
    pure false
  allocateStack := fun _ _ => block "vararg stack"
  copyToMemory := fun _ _ _ => block "vararg copy"
  vaListPtr := fun _ _ => block "vaList"
  writeZeroBytes := fun _ _ _ => block "zero varargs"
  vaListKeyField := fun _ _ => block "vaList key"
  writePointerToMemory := fun _ _ _ => block "vararg pointer"
  pushRaw := fun _ => pushRaw p
  pushDone := fun _ => pushDone p
  popRaw := fun _ => popRaw p
  cleanup := fun _ => cleanup p
  afterFrameInit := fun _ => event "afterFrameInit"
  callExtra := fun _ _ _ _ _ _ _ => block "extra function"
  callIntrinsic := fun _ _ _ _ _ _ => block "intrinsic"
  callLlvmIntrinsic := fun _ _ _ _ _ => block "LLVM intrinsic"
  findMirOrEvalFn := fun _ fnInstance _ _ _ _ _ => do
    let body ← lift ((Input.CallResolution.loadedBodyOfInstance p.resolution fnInstance).mapError StepError.invalidProgram)
    return some (body,fnInstance)
  resolveVirtual := fun _ _ _ _ _ _ => block "virtual resolution"
  isDynamic := fun _ => block "drop dynamic query"
  unpackDynForDrop := fun _ _ => block "dyn drop"
  resolveDropGlue := fun _ _ => block "drop glue"
  mplaceToMutRef := fun _ _ => block "drop reference"
  fakeUnitReturn := fun _ => block "unit return" }

private def controlHooks (p : Program) : TerminatorHooks CtfeProvenance LocalLayout Nat Machine Unit (OpTy CtfeProvenance) (RvalueImmTy CtfeProvenance) := {
  bodySpan := fun frame => (p.bodySpans[frame.extra]?).toExcept (.invalidProgram "body source span")
  returnOperand := fun _ state => runRvalue (evalPlaceOp p.metadata ⟨0,#[]⟩ none) state
  popFrame := fun _ state => runRvalue (popRaw p) state
  copyReturn := fun _ op dest state => runRvalue (copyToRuntime p.metadata op dest) state
  cleanupFrame := fun _ unwinding frame state => runRvalue (cleanup p unwinding frame) state
  unwindTerminate := fun _ _ state => (state,.error (.unsupported "unwind terminate"))
  evalDiscriminant := fun _ _ state => (state,.error (.unsupported "switch"))
  compareSwitchCase := fun _ _ _ state => (state,.error (.unsupported "switch case"))
  call := fun _ term state => runRvalue (Call.evalCallTerminator (callHooks p) () 20 term) state
  tailCall := fun _ term state => runRvalue (do
    event "tailCall"
    Call.evalTailCallTerminator (callHooks p) () 20 term) state
  drop := fun _ _ _ _ state => (state,.error (.unsupported "drop"))
  ignoreOptionalOverflowChecks := fun _ => false
  readAssertCondition := fun _ operand state => runRvalue (readBool p.metadata operand) state
  assertPanic := fun _ _ _ state =>
    ({ state with machine.trace := state.machine.trace ++ ["assertPanic"] },.error (.machineStop "assertion panic")) }
private def stepHooks (p : Program) : StepHooks CtfeProvenance LocalLayout Nat Machine Unit Dest := {
  assign := fun _ place value state => runRvalue (evalRvalueIntoPlace (rvalueHooks p.metadata) () value place) state
  evalPlace := fun _ place skip state => runRvalue (evalDest p.metadata place skip) state
  writeDiscriminant := fun _ _ _ state => (state,.error (.unsupported "write discriminant"))
  storageLive := fun _ localId state => runRvalue (storage p.metadata localId true) state
  storageDead := fun _ localId state => runRvalue (storage p.metadata localId false) state
  intrinsic := fun _ _ state => (state,.error (.unsupported "intrinsic"))
  incrementConstEvalCounter := fun _ state => (state,.error (.unsupported "const eval counter"))
  returnFromCurrentFrame := fun _ unwind => ControlFlow.returnFromCurrentFrame (controlHooks p).toControlHooks () unwind
  beforeTerminator := fun _ state => (state,.ok ())
  terminator := fun _ term => ControlFlow.evalTerminator (controlHooks p) () term }
private def execute (p : Program) : Nat → State → State × Except StepError Unit
  | 0,state => (state,.error (.resourceExhaustion "test fuel"))
  | fuel+1,state =>
    let (state,result) := Step.step (stepHooks p) () state
    match result with
    | .error e => (state,.error e)
    | .ok false => (state,.ok ())
    | .ok true => execute p fuel state
private def initialState (p : Program) (root : Nat) (argument : Nat) : Except StepError State := do
  let definition ← (p.lowered.rootDefinitionId root).mapError StepError.invalidProgram
  let fnInstance : CallInstance := ⟨.Item definition,#[]⟩
  let loaded ← (Input.CallResolution.loadedBodyOfInstance p.resolution fnInstance).mapError StepError.invalidProgram
  let index := loaded.identity.index
  let body ← bodyAt p index
  if (← body.ownDefinitionId.mapError StepError.invalidProgram) != definition then
    throw (.invalidProgram "canonical root instance definition mismatch")
  if body.body.argumentCount != 1 then throw (.unsupported "root argument count")
  let retTy ← body.body.locals[0]?.toExcept (.invalidProgram "return type")
  let argTy ← body.body.locals[1]?.toExcept (.invalidProgram "argument type")
  let retLayout ← lookup p.metadata retTy
  let argLayout ← lookup p.metadata argTy
  let (memory,output) ← GlobalMemory.create p.metadata.target p.lowered.bundle.definitions p.lowered.input.allocations retLayout
  let machine : Machine := { returnMemory := memory, returnPlace := output }
  let span ← p.bodySpans[index]?.toExcept (.invalidProgram "root source span")
  let pushed := Stack.empty.pushStackFrameRaw machine (lifecycle p index) loaded fnInstance (.stop true) (.memory ⟨output.mplace,retLayout⟩) span
  let _ ← pushed.outcome.mapError StepError.stack
  let state : State := ⟨pushed.stack,pushed.state⟩
  let arg ← (ScalarInt.tryFromUInt (BitVec.ofNat 128 argument) argLayout.layout.size).mapError (fun e => .invalidProgram (toString e))
  let arg ← arg.toExcept (.invalidProgram "argument fit")
  let result := runRvalue (do
    storage p.metadata 1 true
    writeLocal p.metadata ⟨1,argLayout⟩ (.scalar (.fromScalarInt arg))
    pushDone p) state
  let _ ← result.2
  pure result.1
private def must (value : Except String A) : IO A :=
  match value with | .ok value => pure value | .error e => throw (IO.userError e)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
private def rootIndex (p : Program) (name : String) : Except String Nat :=
  (p.lowered.input.bodies.toList.findIdx? (·.defPath == name)).toExcept s!"missing root {name}"
private def runCase (p : Program) (name : String) (argument : Nat) : IO (State × Except StepError Unit) := do
  let index ← must (rootIndex p name)
  let initial ← must ((initialState p index argument).mapError reprStr)
  pure (execute p 300 initial)

def main (args : List String) : IO Unit := do
  let path ← match args with | path::_ => pure path | [] => throw (IO.userError "usage: ImportedGlobals <export>")
  let decoded ← must (Input.decodeJson (← IO.FS.readFile path))
  check (decoded.document.producer.targetTriple == "x86_64-unknown-linux-gnu") "fixture target"
  let p ← must ((prepare decoded.document).mapError reprStr)
  let (normal,outcome) ← runCase p "root" 0
  check outcome.isOk s!"global calls failed: {reprStr outcome}"
  check (normal.stack.frames.isEmpty && normal.machine.returned) "root return"
  let (readMemory,read) := GlobalMemory.read p.metadata.target normal.machine.returnMemory normal.machine.returnPlace
  let value ← must (read.mapError reprStr)
  let scalar ← must (value.value.toScalar.mapError reprStr)
  let bits ← must (scalar.toBits value.layout.size |>.mapError reprStr)
  check (bits.toNat == 42) "static read/call result"
  let events := readMemory.events
  check (events.contains "constant-root" && events.contains "initializer" && events.contains "global-access" &&
    events.contains "global-adjust" && events.contains "read") "missing global access chain"
  check (normal.machine.trace.contains "placeDeref" && normal.machine.trace.contains "placeReadRaw" &&
    normal.machine.trace.contains "callerLocalReturn") "missing Place/call connection"
  let rootEvent ← must ((events.toList.idxOf? "constant-root").toExcept "missing root event")
  let initializerEvent ← must ((events.toList.idxOf? "initializer").toExcept "missing initializer event")
  let beforeEvent ← must ((events.toList.idxOf? "global-access").toExcept "missing global event")
  let adjustEvent ← must ((events.toList.idxOf? "global-adjust").toExcept "missing adjust event")
  let readEvent ← must ((events.toList.idxOf? "read").toExcept "missing read event")
  check (rootEvent < initializerEvent && initializerEvent < beforeEvent && beforeEvent < adjustEvent &&
    adjustEvent < readEvent) "global initialization/read hook order"
  check (normal.machine.returnMemory.memory.importedGlobalIds.all (fun (source,runtime) =>
    runtime.value.toNat >= 100 && runtime.value.toNat != source)) "source IDs used as runtime allocation identities"
  check ((events.toList.filter (· == "initializer")).length == 1) "initializer caching/order"
  let (panic,panicOutcome) ← runCase p "root" 4294967295
  check (panicOutcome == Except.error (StepError.machineStop "assertion panic")) "global-based overflow did not panic"
  check (!panic.machine.returned && panic.machine.trace.contains "assertPanic") "panic became success"
  let root ← must (rootIndex p "root")
  let initial ← must ((initialState p root 0).mapError reprStr)
  let missingMemory := Miri.Memory.MemoryState.setGlobalEntries
    initial.machine.returnMemory.memory #[]
  let missingGlobals := { initial with machine.returnMemory := {
      initial.machine.returnMemory with memory := missingMemory } }
  let (_,missing) := execute p 300 missingGlobals
  check (!missing.isOk) "missing global accepted"
  let noData := { p with lowered.input.allocations := #[] }
  let noDataInitial ← must ((initialState noData root 0).mapError reprStr)
  let (_,noDataOutcome) := execute noData 300 noDataInitial
  check (!noDataOutcome.isOk) "missing allocation image accepted"
  let invalidData := { p with lowered.input.allocations := p.lowered.input.allocations.map fun node =>
    match node.data with
    | some (.static source) => { node with data := some (.static { source with
        initializer := match source.initializer with
          | none => none
          | some initializer => some { initializer with bytesHex := "ff" } }) }
    | _ => node }
  check (!(initialState invalidData root 0).isOk) "invalid initializer bytes accepted"
  let uninitialized := { p with lowered.input.allocations := p.lowered.input.allocations.map fun node =>
    match node.data with
    | some (.static source) => { node with data := some (.static { source with
        initializer := match source.initializer with
          | none => none
          | some initializer => some { initializer with initializationRanges := #[⟨false,0,4⟩] } }) }
    | _ => node }
  let uninitState ← must ((initialState uninitialized root 0).mapError reprStr)
  let (_,uninitOutcome) := execute uninitialized 300 uninitState
  check (!uninitOutcome.isOk) "uninitialized static scalar read accepted"
  let sourceStatic ← must ((p.lowered.input.allocations.find? fun node => match node.data with
    | some (.static _) => true | _ => false).toExcept "missing fixture static")
  let staticId ← must (Input.AllocationImage.runtimeId initial.machine.returnMemory.memory sourceStatic.id)
  let provenance ← must ((CtfeProvenance.fromAllocId staticId).mapError reprStr)
  let uintLayout ← must (((p.metadata.integerLayout .u32).mapError metadataError).mapError reprStr)
  let staticPlace : MemoryOperandPlace CtfeProvenance :=
    ⟨⟨⟨Size.ZERO,some provenance⟩,.none,none⟩,localMemoryLayout uintLayout⟩
  let (_,staticWrite) := GlobalMemory.write p.metadata.target initial.machine.returnMemory staticPlace
    (.scalar (.fromScalarInt (ScalarInt.ofUInt32 99)))
  check (!staticWrite.isOk) "immutable static write accepted"
  IO.println "global_call=42"
  IO.println "global_overflow=panic"
  IO.println "actual global Constant/AllocationImage -> Place/memory -> nested calls -> return allocation; missing/invalid data rejected"
