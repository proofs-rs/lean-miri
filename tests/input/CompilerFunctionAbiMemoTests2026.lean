import Miri.Input.CallResolution

open Lean Miri.Input

private def must {α : Type} (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def candidate (raw : Json) : Bool :=
  ["arguments", "return", "calling_convention", "can_unwind", "c_variadic", "fixed_count"]
    |>.all fun key => (raw.getObjVal? key).isOk

private def set (value : Json) (key : String) (child : Json) : Except String Json := do
  let fields ← value.getObj?
  pure (Json.mkObj ((key, child) :: fields.toList.filter (fun item => item.1 != key)))

private def sameAttributes (left right : AbiAttributes) : Bool :=
  left.noAlias == right.noAlias && left.noFree == right.noFree &&
  left.noUndef == right.noUndef && left.nonNull == right.nonNull &&
  left.readOnly == right.readOnly && left.writable == right.writable &&
  left.inRegister == right.inRegister && left.regularBits == right.regularBits &&
  left.pointeeSizeBytes == right.pointeeSizeBytes &&
  left.pointeeAlignBytes == right.pointeeAlignBytes &&
  left.argExtension.payload == right.argExtension.payload &&
  left.captures.payload == right.captures.payload

private def sameLayout (left right : Layout) : Bool :=
  left.status == right.status && left.kind == right.kind &&
  left.sizeBytes == right.sizeBytes && left.abiAlignBytes == right.abiAlignBytes &&
  left.unadjustedAbiAlignBytes == right.unadjustedAbiAlignBytes &&
  left.fieldOffsetsBytes == right.fieldOffsetsBytes &&
  left.variantsKind == right.variantsKind && left.backendReprKind == right.backendReprKind &&
  left.fields.map (·.payload) == right.fields.map (·.payload) &&
  left.variantsLayout.map (·.payload) == right.variantsLayout.map (·.payload) &&
  left.backendRepresentation.map (·.payload) == right.backendRepresentation.map (·.payload) &&
  left.payload == right.payload

private def sameMode (left right : AbiPassMode) : Bool :=
  left.kind == right.kind && left.attributes.size == right.attributes.size &&
  ((List.range left.attributes.size).all fun i =>
    match left.attributes[i]?, right.attributes[i]? with
    | some l, some r => sameAttributes l r
    | _, _ => false) &&
  left.castTarget.map (·.payload) == right.castTarget.map (·.payload) &&
  left.padI32Count == right.padI32Count && left.addressSpace == right.addressSpace &&
  left.indirectMode.map (·.payload) == right.indirectMode.map (·.payload) &&
  left.payload == right.payload

private def sameArgument (left right : AbiArgument) : Bool :=
  left.typeId == right.typeId && left.payload == right.payload &&
  sameMode left.mode right.mode && left.layout.isSome == right.layout.isSome &&
  (match left.layout, right.layout with
  | some l, some r => sameLayout l r
  | none, none => true
  | _, _ => false)

/- Compare every exposed ABI field used by this decoder path. The existing
   SharedFunctionAbiTests additionally compares converted FnAbi outcomes. -/
private def sameAbiProjection (left right : FunctionAbi) : Bool :=
  left.payload == right.payload && left.arguments.size == right.arguments.size &&
  ((List.range left.arguments.size).all fun i =>
    match left.arguments[i]?, right.arguments[i]? with
    | some l, some r => sameArgument l r
    | _, _ => false) &&
  sameArgument left.returnValue right.returnValue &&
  left.callingConvention.status == right.callingConvention.status &&
  left.callingConvention.kind == right.callingConvention.kind &&
  left.callingConvention.armCall == right.callingConvention.armCall &&
  left.callingConvention.interruptKind == right.callingConvention.interruptKind &&
  left.callingConvention.x86Call == right.callingConvention.x86Call &&
  left.callingConvention.payload == right.callingConvention.payload &&
  left.canUnwind == right.canUnwind && left.cVariadic == right.cVariadic &&
  left.fixedCount == right.fixedCount

private def replaceArgument (abi : Json) (index : Nat) (key : String) (value : Json) : Except String Json := do
  let args ← (← abi.getObjVal? "arguments").getArr?
  let some arg := args[index]? | throw "test ABI has no selected argument"
  let arg ← set arg key value
  let args := args.set! index arg
  set abi "arguments" (.arr args)

private def replaceReturn (abi : Json) (key : String) (value : Json) : Except String Json := do
  let arg ← abi.getObjVal? "return"
  set abi "return" (← set arg key value)

private def badLayout : Json := Json.mkObj [
  ("status", toJson ("supported" : String)),
  ("field_offsets_bytes", toJson ("not-an-array" : String))]

private def duplicateStatusLayout : Json := Id.run do
  let emptyNode : Std.DTreeMap.Internal.Impl String (fun _ : String => Json) := .leaf
  let duplicateStatus : Std.DTreeMap.Internal.Impl String (fun _ : String => Json) :=
    .inner 1 "status" (.str "incomplete") emptyNode emptyNode
  let status : Std.DTreeMap.Internal.Impl String (fun _ : String => Json) :=
    .inner 2 "status" (.str "incomplete") emptyNode duplicateStatus
  let root : Std.DTreeMap.Internal.Impl String (fun _ : String => Json) :=
    .inner 3 "field_offsets_bytes" (.arr #[]) emptyNode status
  Json.obj ⟨⟨root⟩⟩

private def incompleteLayout (size : Nat) : Json := Json.mkObj [
  ("status", toJson ("incomplete" : String)),
  ("field_offsets_bytes", Json.arr #[]),
  ("size_bytes", toJson size)]

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected exporter mir_features.json")
  let decoded ← must (decodeRuntimeJson (← IO.FS.readFile path))
  let nodes := decoded.document.sharedNodes
  let memo := prepareCompilerFunctionAbiMemo nodes
  let some importedAbis := decoded.document.compilerFunctionAbiTable |
    throw (IO.userError "import omitted typed compiler ABI queries")
  for (raw, result) in importedAbis.entries do
    match result, decodeCompilerFunctionAbi raw with
    | .ok a, .ok b => check (sameAbiProjection a b) "import-time typed ABI differs"
    | .error a, .error b => check (a == b) "import-time deferred ABI error differs"
    | _, _ => throw (IO.userError "import-time ABI result class differs")
  let mut candidateCount := 0
  let mut sample? : Option Json := none
  for raw in nodes do
    if candidate raw then
      let direct := decodeCompilerFunctionAbi raw
      let cached := decodeCompilerFunctionAbiWithMemo raw memo
      match direct, cached with
      | .ok left, .ok right =>
        check (sameAbiProjection left right) "cached FunctionAbi projection differs from direct decode"
        if sample?.isNone && !left.arguments.isEmpty then sample? := some raw
      | .error left, .error right =>
        check (left == right) s!"cached ABI error path changed: {left} != {right}"
      | _, _ => throw (IO.userError "cached and direct ABI decoders disagree on success")
      candidateCount := candidateCount + 1
  check (candidateCount > 0 && sample?.isSome) "fixture has no usable FnAbi candidate"
  -- The import-time complete-value memo must agree with the independent
  -- demand decoder, including failures and fallback on a changed source value.
  let some valueMemo := decoded.document.compilerValueMemo |
    throw (IO.userError "import omitted the compiler value memo")
  let mut valueCount := 0
  for node in nodes do
    if let .obj fields := node then
      for (key, raw) in fields.toList do
        if ["generic_args", "rebased_args", "span", "preamble_def_span", "callsite_span"].contains key then
          let direct := decodeCompilerValue raw
          let cached := decodeCompilerValueWithMemo raw (some valueMemo)
          let agrees := match direct, cached with
            | .ok a, .ok b => a == b
            | .error a, .error b => a == b
            | _, _ => false
          check agrees s!"import-time compiler value differs at {key}"
          valueCount := valueCount + 1
  check (valueCount > 0) "fixture has no compiler values"
  let malformedSpan := Json.mkObj [("lo", .str "bad"), ("hi", toJson (0 : Nat)),
    ("start", .null), ("end", .null), ("context", .str "x"), ("file", .str "x")]
  let fallback := decodeCompilerValueWithMemo malformedSpan (some valueMemo)
  let sameFallback := match fallback, decodeCompilerValue malformedSpan with
    | .ok a, .ok b => a == b
    | .error a, .error b => a == b
    | _, _ => false
  check sameFallback "compiler value fallback diagnostic changed"
  let sample := sample?.get!

  let malformedKey := duplicateStatusLayout
  let malformedValue ← must (decodeCompilerLayout malformedKey)
  let malformedFields ← must (malformedKey.getObj?)
  let mut collision? : Option (Nat × Layout) := none
  for size in [:10000] do
    if collision?.isNone then
      let validKey := incompleteLayout size
      let validFields ← must (validKey.getObj?)
      if malformedFields.toList.length == validFields.toList.length &&
          malformedKey == validKey && !(validKey == malformedKey) then
        let emptyCache : Std.HashMap Json Layout := {}
        let bareCache := emptyCache.insert malformedKey malformedValue
        if let some found := bareCache[validKey]? then
          if found.sizeBytes != some size then collision? := some (size, found)
  let some (size, poisoned) := collision? |
    throw (IO.userError "could not find a HashMap collision with a valid key for the asymmetric malformed layout key")
  check (poisoned.sizeBytes.isNone) "malformed cache collision did not return the incomplete layout"
  let validKey := incompleteLayout size
  let validValue ← must (decodeCompilerLayout validKey)
  check (validValue.sizeBytes == some size) "valid test layout did not retain its explicit size"
  let abiWithValidLayout ← must (replaceReturn sample "layout" validKey)
  let guardedMemo := prepareCompilerFunctionAbiMemo #[validKey]
  let directValid ← must (decodeCompilerFunctionAbi abiWithValidLayout)
  let cachedValid ← must (decodeCompilerFunctionAbiWithMemo abiWithValidLayout guardedMemo)
  check (sameAbiProjection directValid cachedValid &&
    cachedValid.returnValue.layout.map (·.sizeBytes) == some (some size))
    "guarded ABI memo returned an incomplete/colliding Layout instead of the exact valid value"

  let malformedArgument ← must (replaceArgument sample 0 "layout" badLayout)
  let malformedReturn ← must (replaceReturn sample "layout" badLayout)
  let malformedMemo := prepareCompilerFunctionAbiMemo #[badLayout]
  let argumentDirect := decodeCompilerFunctionAbi malformedArgument
  let argumentCached := decodeCompilerFunctionAbiWithMemo malformedArgument malformedMemo
  let returnDirect := decodeCompilerFunctionAbi malformedReturn
  let returnCached := decodeCompilerFunctionAbiWithMemo malformedReturn malformedMemo
  match argumentDirect, argumentCached, returnDirect, returnCached with
  | .error a, .error b, .error c, .error d =>
    check (a == b && c == d) "failed layout memo changed the exact decoder diagnostic"
    check (a.contains "arguments[0].layout.field_offsets_bytes" &&
      c.contains "return.layout.field_offsets_bytes")
      s!"malformed layout error lost current occurrence path: argument={a}; return={c}"
  | _, _, _, _ => throw (IO.userError "malformed layouts unexpectedly decoded")

  let metadata ← must ((RuntimeMetadata.ofDocument decoded.document).mapError toString)
  let mut rawSample? : Option Json := none
  let mut decoy? : Option FunctionAbi := none
  for raw in nodes do
    if candidate raw && rawSample?.isNone then
      match decodeCompilerFunctionAbi raw with
      | .ok value =>
        rawSample? := some raw
        decoy? := some { value with callingConvention :=
          { value.callingConvention with kind := .unknown "deliberate-decoy" } }
      | .error _ => pure ()
  let some raw := rawSample? | throw (IO.userError "fixture has no decoy ABI candidate")
  let some decoy := decoy? | throw (IO.userError "fixture ABI could not form a decoy projection")
  let manual : RuntimeMetadata := { metadata with source :=
    { metadata.source with functionAbis := #[decoy] } }
  let cache := CallResolution.prepareFunctionAbiCache manual
  let direct := CallResolution.functionAbiJson manual raw
  let cached := CallResolution.functionAbiJson manual raw (some cache)
  check (direct.isOk && cached == direct)
    "ABI cache trusted a misleading source.functionAbis projection instead of decoding raw shared nodes"
  let argsJson ← must (sample.getObjVal? "arguments")
  let args ← must argsJson.getArr?
  let malformedArity ← must (set sample "fixed_count" (toJson (args.size + 1)))
  let manualWithBadArity : RuntimeMetadata := { manual with source :=
    { manual.source with sharedNodes := manual.source.sharedNodes.push malformedArity, compilerFunctionAbiTable := none } }
  let arityCache := CallResolution.prepareFunctionAbiCache manualWithBadArity
  let arityDirect := CallResolution.functionAbiJson manualWithBadArity malformedArity
  let arityCached := CallResolution.functionAbiJson manualWithBadArity malformedArity (some arityCache)
  let arityErrorMatches := match arityDirect with
    | .error error => error.contains "fixed_count exceeds actual arguments"
    | .ok _ => false
  check (arityErrorMatches && arityCached == arityDirect)
    "memoized ABI path bypassed fixed-count arity validation"

  let arityTable := DecoderValues.prepareCompilerFunctionAbiTableUsing manualWithBadArity.source.sharedNodes
    (DecoderValues.sharedDecodeMemo manualWithBadArity.source.sharedNodes)
  let typedArity : RuntimeMetadata := { manualWithBadArity with source :=
    { manualWithBadArity.source with compilerFunctionAbiTable := some arityTable } }
  let typedArityCache := CallResolution.prepareFunctionAbiCache typedArity
  check (CallResolution.functionAbiJson typedArity malformedArity (some typedArityCache) == arityDirect)
    "import-time ABI projection bypassed runtime arity validation"

  let returnJson ← must (sample.getObjVal? "return")
  let returnLayout ← must (returnJson.getObjVal? "layout")
  let oversizedLayout ← must (set returnLayout "size_bytes" (toJson (2^64 : Nat)))
  let oversizedAbi ← must (replaceReturn sample "layout" oversizedLayout)
  let mut sizeNodes := manual.source.sharedNodes
  sizeNodes := sizeNodes.push oversizedLayout
  sizeNodes := sizeNodes.push oversizedAbi
  let manualWithOversizedLayout : RuntimeMetadata := { manual with source :=
    { manual.source with sharedNodes := sizeNodes, compilerFunctionAbiTable := none } }
  let sizeCache := CallResolution.prepareFunctionAbiCache manualWithOversizedLayout
  let sizeDirect := CallResolution.functionAbiJson manualWithOversizedLayout oversizedAbi
  let sizeCached := CallResolution.functionAbiJson manualWithOversizedLayout oversizedAbi (some sizeCache)
  let sizeErrorMatches := match sizeDirect with
    | .error error => error.contains "u64 overflow"
    | .ok _ => false
  check (sizeErrorMatches && sizeCached == sizeDirect)
    "memoized ABI path bypassed manual-runtime physical layout size validation"
  let sizeTable := DecoderValues.prepareCompilerFunctionAbiTableUsing sizeNodes
    (DecoderValues.sharedDecodeMemo sizeNodes)
  let typedSize : RuntimeMetadata := { manualWithOversizedLayout with source :=
    { manualWithOversizedLayout.source with compilerFunctionAbiTable := some sizeTable } }
  let typedSizeCache := CallResolution.prepareFunctionAbiCache typedSize
  check (CallResolution.functionAbiJson typedSize oversizedAbi (some typedSizeCache) == sizeDirect)
    "import-time ABI projection bypassed runtime layout-size validation"
  IO.println s!"CompilerFunctionAbiMemoTests: {candidateCount} candidates; collision safety, exact sizes, error paths, manual metadata, and arity validation passed"
