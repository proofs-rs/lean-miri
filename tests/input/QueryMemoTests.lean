import Miri.Input.Decoder
import Miri.Input.CompilerProviders
import Miri.Input.CompilerSignatureAbi

open Lean Miri.Input Miri.Interpreter

private def must (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

-- Separate IO invocations model run entry; repeating a pure constructor expression
-- can share the expression and does not establish a second invocation.
@[noinline] private def fresh (prepared : CompilerProviders.Prepared) : IO CompilerProviders.Prepared :=
  pure prepared.startSession

@[noinline] private def freshRuntime (runtime : RuntimeMetadata) : IO RuntimeMetadata :=
  pure runtime.startSession

@[noinline] private def query (runtime : RuntimeMetadata) (id : TypeId) :
    IO (RuntimeMetadata.Result (Miri.ABI.TyAndLayout TypeId)) :=
  pure (runtime.lookup id)

@[noinline] private def instanceQuery (prepared : CompilerInstanceAbi.Prepared) (id : InstanceId)
    (extra : Array TypeId := #[]) : IO (Except String (Miri.ABI.FnAbi TypeId)) :=
  pure (CompilerInstanceAbi.abiOfInstance prepared id extra)

private def sameResult [DecidableEq α] (left right : α) (message : String) : IO Unit :=
  check (decide (left = right)) message

unsafe def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected current source-material input")
  let input ← must (← decodeFile path)
  let document := input.document
  let runtime ← must (RuntimeMetadata.ofDocument document |>.mapError toString)
  let session := runtime.startSession
  for node in document.types do
    sameResult (session.lookup node.id) (runtime.lookup node.id) "layout session changed canonical result"
  for id in #[document.types.size, document.types.size + 1, 2^64] do
    sameResult (session.lookup id) (runtime.lookup id) "invalid layout ID changed error"
  let program ← must (lowerProgram document)
  let abi ← must (CompilerInstanceAbi.prepare runtime program)
  let memo := CompilerInstanceAbi.startSession abi session
  for id in List.range document.instances.size do
    for extra in #[#[], #[0], #[0, 0], #[document.types.size]] do
      sameResult (CompilerInstanceAbi.abiOfInstance memo id extra)
        (SourceAbiRuntime.ofInstance runtime id extra) "ABI session changed complete-key canonical result"
  for id in #[document.instances.size, 2^64] do
    sameResult (CompilerInstanceAbi.abiOfInstance memo id #[])
      (SourceAbiRuntime.ofInstance runtime id #[]) "invalid ABI ID changed error"
  let some base := document.types[0]? | throw (IO.userError "fixture has no type")
  let cyclic := {base with shape := .tuple #[0], sourceLayout := {base.sourceLayout with normalizedType := 0}}
  let alias := {base with id := 1, sourceLayout := {base.sourceLayout with normalizedType := 0}}
  let badDocument := {document with types := #[cyclic, alias]}
  let badRuntime ← must (RuntimeMetadata.ofDocument badDocument |>.mapError toString)
  let badSession ← freshRuntime badRuntime
  for id in #[0, 1] do
    let expected := badRuntime.lookup id
    sameResult (badSession.lookup id) expected "cached layout error changed"
    let .error error := expected | throw (IO.userError "cyclic layout unexpectedly succeeded")
    let .invalid label _ := error | throw (IO.userError "cyclic layout error lost its classification")
    check (label == s!"concrete layout for type {id}") "normalization alias lost requested-ID error prefix"
  let first ← query badSession 0
  let again ← query badSession 0
  check (ptrEq first again) "repeated layout error did not reuse its session result"
  let otherSession ← freshRuntime badRuntime
  let other ← query otherSession 0
  check (!(ptrEq first other)) "fresh layout session reused the previous session result"
  let prepared ← must (CompilerProviders.prepare program)
  let one ← fresh prepared
  let two ← fresh prepared
  check (!(ptrEq one.runtime two.runtime)) "fresh invocations shared their runtime owner"
  check (ptrEq one.runtime.source prepared.runtime.source && ptrEq two.runtime.source prepared.runtime.source)
    "fresh query sessions did not reuse their validated input material"
  check (ptrEq one.runtime.target prepared.runtime.target && ptrEq two.runtime.target prepared.runtime.target)
    "fresh query sessions re-imported their target"
  let selected := document.types.findIdx? fun node => match node.shape with
    | .reference .. | .rawPointer .. | .adt .. | .tuple _ => true
    | _ => false
  let some id := selected | throw (IO.userError "fixture has no composite type")
  let value ← query one.runtime id
  for view in #[one.lifecycle.instances.runtime, one.lifecycle.shim.runtime, one.lifecycle.calls.calls.runtime,
      one.lifecycle.calls.symbols.facts.context.runtime, one.lifecycle.frames.calls.calls.runtime,
      one.functions.runtime, one.main.runtime, one.namedConstants.runtime, one.namedGlobals.runtime,
      one.externStatics.runtime, one.pointers.calls.calls.runtime, one.vtables.calls.calls.runtime,
      one.vtables.queries.facts.context.runtime, one.namedAbi.runtime] do
    check (ptrEq one.runtime view) "provider view used a different session owner"
    let actual ← query view id
    check (ptrEq value actual) "runtime-bearing provider view did not use the shared session cache"
  if let .ok arrays := one.initialArrays then
    let actual ← query arrays.metadata id
    check (ptrEq value actual) "runtime-array provider retained the previous metadata cache"
  let secondValue ← query two.runtime id
  sameResult secondValue (runtime.lookup id) "second session changed layout semantics"
  check (!(ptrEq value secondValue)) "same Prepared reused its layout result across runs"
  let some definition := document.sourceAbi.bind (·.definitions.findSome? (fun value => value))
    | throw (IO.userError "fixture has no ABI definition")
  let firstAbi ← instanceQuery one.lifecycle.instances definition.instanceId
  let againAbi ← instanceQuery one.lifecycle.instances definition.instanceId
  check (ptrEq firstAbi againAbi) "repeated ABI query did not reuse the session result"
  let secondAbi ← instanceQuery two.lifecycle.instances definition.instanceId
  sameResult firstAbi secondAbi "fresh ABI session changed result"
  check (!(ptrEq firstAbi secondAbi)) "same Prepared reused its ABI result across runs"
  let some material := document.sourceAbi | throw (IO.userError "missing source ABI material")
  let some wide := document.types.find? (fun node => match node.shape with
    | .uint (.known .u64) => true | _ => false) | throw (IO.userError "missing u64")
  let some narrow := document.types.find? (fun node => match node.shape with
    | .uint (.known .u8) => true | _ => false) | throw (IO.userError "missing u8")
  let some unit := document.types.find? (fun node => match node.shape with
    | .tuple fields => fields.isEmpty | _ => false) | throw (IO.userError "missing unit")
  let missingMaterial := {material with definitions := material.definitions.set! definition.instanceId none}
  let missingRuntime ← must (RuntimeMetadata.ofDocument
    {document with sourceAbi := some missingMaterial} |>.mapError toString)
  let missingPrepared := CompilerInstanceAbi.startSession
    (← must (CompilerInstanceAbi.prepare missingRuntime program)) missingRuntime.startSession
  for extra in #[#[], #[wide.id]] do
    sameResult (CompilerInstanceAbi.abiOfInstance missingPrepared definition.instanceId extra)
      (.error "missing concrete instance source ABI signature") "missing definition error prefix changed"
  let rustSignature := {definition.signature with
    inputs := #[wide.id], output := unit.id, abi := .Rust, cVariadic := false, splatted := none}
  let runtimeFor := fun signature policy neverUnwind =>
    let row := {definition with
      signature, neverUnwind, hasDefinition := true, foreign := false, dropGlue := false, virtualCall := false, callerLocation := none}
    let source := {material with
      policy, definitions := material.definitions.set! definition.instanceId (some row)}
    RuntimeMetadata.ofDocument {document with sourceAbi := some source} |>.mapError toString
  let unwinding ← must (runtimeFor rustSignature {material.policy with panicUnwinds := true} false)
  let aborting ← must (runtimeFor rustSignature {material.policy with panicUnwinds := false} false)
  let never ← must (runtimeFor rustSignature {material.policy with panicUnwinds := true} true)
  let mut unwindValues := #[]
  for owner in #[unwinding, aborting, never] do
    let cached := CompilerInstanceAbi.startSession (← must (CompilerInstanceAbi.prepare owner program)) owner.startSession
    let canonical := SourceAbiRuntime.ofInstance owner definition.instanceId #[]
    sameResult (CompilerInstanceAbi.abiOfInstance cached definition.instanceId #[]) canonical
      "ABI material/policy scope retained a different owner's result"
    unwindValues := unwindValues.push (← must canonical).canUnwind
  check (unwindValues == #[true, false, false]) "policy/definition control failed to distinguish ABI results"
  let variadic := {rustSignature with abi := .C false, cVariadic := true}
  let varRuntime ← must (runtimeFor variadic material.policy false)
  let varPrepared := CompilerInstanceAbi.startSession
    (← must (CompilerInstanceAbi.prepare varRuntime program)) varRuntime.startSession
  let mut variants := #[]
  for extra in #[#[], #[narrow.id], #[wide.id], #[wide.id, narrow.id], #[document.types.size]] do
    let actual := CompilerInstanceAbi.abiOfInstance varPrepared definition.instanceId extra
    sameResult actual (SourceAbiRuntime.ofInstance varRuntime definition.instanceId extra)
      "nonempty varargs fallback changed ordered extra arguments or errors"
    variants := variants.push actual
  check (decide (variants[1]! ≠ variants[2]!)) "different vararg types acquired the same ABI"
  check (decide (variants[2]! ≠ variants[3]!)) "different vararg counts acquired the same ABI"
  for signature in #[rustSignature, variadic, {variadic with abi := .C true},
      {rustSignature with output := wide.id}, {rustSignature with inputs := #[]},
      {rustSignature with safety := .Unsafe}, {rustSignature with splatted := some 0}] do
    for extra in #[#[], #[wide.id]] do
      sameResult (SourceAbiRuntime.ofSignature runtime.startSession signature extra)
        (SourceAbiRuntime.ofSignature runtime signature extra)
        "uncached signature ABI changed its full request"
  let request : FunctionCalls.SignatureRequest Miri.ABI.ExternAbi := {
    inputs := #[wide.id], output := unit.id, abi := .Rust,
    safety := .Safe, cVariadic := false, splatted := true }
  sameResult (CompilerSignatureAbi.query one request)
    (.error "helper signature must be unsplatted") "helper ABI error boundary moved behind a cache"
  let some target := document.runtimeTargetDataLayout | throw (IO.userError "missing target evidence")
  let changedTarget := {target with i64AlignBytes := if target.i64AlignBytes == 4 then 8 else 4}
  let targetRuntime ← must (RuntimeMetadata.ofDocument
    {document with runtimeTargetDataLayout := some changedTarget} |>.mapError toString)
  let originalLayout ← must (runtime.lookup wide.id |>.mapError toString)
  let targetLayout ← must (targetRuntime.startSession.lookup wide.id |>.mapError toString)
  check (decide (originalLayout.layout.align ≠ targetLayout.layout.align)) "layout cache leaked across target scopes"
  IO.println "query memo: canonical errors/results, aliases, provider/run owners, ABI policies, ordered varargs, signatures and target scope checked"
