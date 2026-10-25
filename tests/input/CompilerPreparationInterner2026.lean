import Miri.Input.CompilerConstantQueries
import Miri.Input.CompilerLifecycle
import Miri.Input.Decoder
import Miri.Input.LowerMIR

/-! Compare the incremental constant/lifecycle preparation path against the
previous ordered-scan implementation on an actual mir_features export. -/
open Lean Miri.Input Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key
private def natural (j : Json) (key : String) : Except String Nat := do (← field j key).getNat?
private def array (j : Json) (key : String) : Except String (Array Json) := do (← field j key).getArr?
private def arrayOrEmpty (j : Json) : Array Json := (j.getArr?).toOption.getD #[]

private partial def constants (j : Json) (path : Array CompilerConstantQueries.PathElement := #[]) :
    Array (Array CompilerConstantQueries.PathElement × Json) :=
  if ((j.getObjVal? "constant").bind (fun c => c.getObjValAs? String "kind")).toOption == some "evaluated_const" then
    #[(path,j)]
  else match j with
  | .arr values => (values.mapIdx fun i value => constants value (path.push (.index i))).flatten
  | .obj fields => (fields.toList.toArray.map fun (name,value) => constants value (path.push (.field name))).flatten
  | _ => #[]

private def sourceConstants (bodyIndex : Nat) (body : Json) :
    Except String (Array (CompilerConstantQueries.Site × Json)) := do
  let mut found := #[]
  for block in ← array body "basic_blocks" do
    let blockId ← natural block "block"
    let statements ← array block "statements"
    for i in [:statements.size] do
      let some statement := statements[i]? | throw "statement array changed"
      for (path,value) in constants statement do
        found := found.push (⟨bodyIndex, ⟨blockId,i⟩, path⟩,value)
    for (path,value) in constants (← field block "terminator") do
      found := found.push (⟨bodyIndex, ⟨blockId,statements.size⟩, path⟩,value)
  pure found

private def lookupPath (j : Json) (path : Array CompilerConstantQueries.PathElement) : Except String Json :=
  path.foldlM (fun value key => match key with
    | .field name => field value name
    | .index i => do
      let values ← value.getArr?
      match values[i]? with
      | some value => pure value
      | none => throw "normalized query changed operand structural path") j

private def siteEnvelope (body : Json) (site : CompilerConstantQueries.Site) : Except String Json := do
  let blocks ← array body "basic_blocks"
  let some block := blocks.find? (fun b => (natural b "block").toOption == some site.location.block)
    | throw "body is missing source basic block"
  let statements ← array block "statements"
  if site.location.statementIndex == statements.size then field block "terminator"
    else match statements[site.location.statementIndex]? with
      | some statement => pure statement
      | none => throw "body is missing source statement"

private def normalizedOperand (body : Json) (site : CompilerConstantQueries.Site) : Except String Json := do
  let envelope ← siteEnvelope body site
  lookupPath envelope site.path

private def legacyEvidenceAt (ctx : LowerContext) (tables : CompilerTables)
    (fnInstance : CallInstance) (site : CompilerConstantQueries.Site)
    (original normalized : Json) : Except String (CompilerConstantQueries.Evidence × CompilerTables) := do
  unless (← field original "span") == (← field normalized "span") do
    throw "normalization changed constant source span"
  let (source,tables) ← lowerCompilerConstOperand ctx tables (← decodeCompilerValue original)
  let (normal,tables) ← lowerCompilerConstOperand ctx tables (← decodeCompilerValue normalized)
  let evaluated ← field normalized "constant"
  unless (← evaluated.getObjValAs? String "status") == "supported" do
    throw "compiler Const::eval did not produce a value"
  let ty ← natural (← field normalized "type") "type_id"
  let value ← lowerCompilerConstValue ctx ty (← decodeCompilerValue (← field evaluated "value"))
  pure (⟨site, ⟨fnInstance,source.value,normal.value,normal.span,value⟩,original,normalized⟩,tables)

private def legacyConstantsPrepare (input : LoweredProgram) : Except String CompilerConstantQueries.Prepared := do
  let mut program := CompilerGlobals.prepareProgram input
  let mut tables := program.compilerTables
  let mut evidence := #[]
  let mut obligations := #[]
  let ctx := LowerContext.ofDocument program.input
  for bodyIndex in [:program.bundle.bodies.size] do
    let some body := program.bundle.bodies[bodyIndex]? | throw "body index missing"
    match field body.input.payload "constant_query_context" with
    | .error _ =>
      obligations := obligations.push ⟨s!"bodies[{bodyIndex}].constant_query_context",
        "compiler current-instance normalization query is missing"⟩
    | .ok queryContext => do
      let (fnInstance,nextTables) ← CompilerInstance.decode ctx tables queryContext
      tables := nextTables
      let normalization ← field queryContext "normalization"
      if (normalization.getObjValAs? String "status").toOption != some "supported" then
        obligations := obligations.push ⟨s!"bodies[{bodyIndex}].constant_query_context",
          "compiler current-instance normalization query failed"⟩
      else
        let normalizedBody ← NormalizationBody.resolve normalization body.input.payload
        for (site,original) in ← sourceConstants bodyIndex body.input.payload do
          let result := do
            let normalized ← normalizedOperand normalizedBody site
            legacyEvidenceAt ctx tables fnInstance site original normalized
          match result with
          | .ok (entry,nextTables) =>
            evidence := evidence.push entry
            tables := nextTables
          | .error message =>
            obligations := obligations.push
              ⟨s!"bodies[{bodyIndex}].constant[{reprStr site.location},{reprStr site.path}]",message⟩
  program := program.withCompilerTables tables
  pure ⟨program,evidence,obligations⟩

private def legacyLifecycleChecks (ctx : LowerContext) (tables : CompilerTables)
    (callee : CallInstance) (payload : Json) :
    Except String (Array (Except StepError CompilerConstantEvidence) × CompilerTables) := do
  let original ← (← payload.getObjVal? "required_consts").getArr?
  let query ← (← payload.getObjVal? "constant_query_context").getObjVal? "required_constant_checks"
  unless (← (← query.getObjVal? "status").getStr?) == "supported" do
    throw s!"unresolved compiler lifecycle query: {query.compress}"
  unless (← (← query.getObjVal? "typing_env").getStr?) == "body_typing_env" do
    throw "required-constant typing environment mismatch"
  let checks ← (← query.getObjVal? "checks").getArr?
  unless checks.size == original.size do throw "required-constant query count mismatch"
  let mut tables := tables
  let mut evidence := #[]
  for index in [:checks.size] do
    let some check := checks[index]? | throw "required check absent"
    let some source := original[index]? | throw "required source operand absent"
    unless (← (← check.getObjVal? "index").getNat?) == index do
      throw "required-constant source order mismatch"
    unless (← check.getObjVal? "span") == (← source.getObjVal? "span") do
      throw "required-constant source span mismatch"
    let result ← check.getObjVal? "result"
    if ((result.getObjVal? "status").bind Json.getStr?).toOption == some "supported" then
      let normalized ← result.getObjVal? "normalized_operand"
      unless (← normalized.getObjVal? "span") == (← source.getObjVal? "span") do
        throw "required constant normalization changed source span"
      let (source,tables') ← lowerCompilerConstOperand ctx tables (← decodeCompilerValue source)
      let (normal,tables') ← lowerCompilerConstOperand ctx tables' (← decodeCompilerValue normalized)
      let ty ← (← normalized.getObjVal? "type").getObjValAs? Nat "type_id"
      let value ← lowerCompilerConstValue ctx ty (← decodeCompilerValue (← result.getObjVal? "value"))
      tables := tables'
      evidence := evidence.push (.ok ⟨callee,source.value,normal.value,normal.span,value⟩)
    else
      let kind := ((result.getObjVal? "kind").bind Json.getStr?).toOption
      let error := if kind == some "required_const_normalization_error" ||
          kind == some "required_const_evaluation_error" then
        StepError.invalidProgram s!"required constant compiler failure: {result.compress}"
        else StepError.unsupported s!"required constant unresolved: {result.compress}"
      evidence := evidence.push (.error error)
  pure (evidence,tables)

private def legacyLifecyclePrepare (program : LoweredProgram) : CompilerLifecycle.Prepared := Id.run do
  let ctx := LowerContext.ofDocument program.input
  let mut tables := program.compilerTables
  let mut entries := #[]
  for body in program.bundle.bodies do
    let preamble := do
      lowerCompilerSpan tables (← decodeCompilerValue (← body.input.payload.getObjVal? "preamble_def_span"))
    let preamble ← match preamble with
      | .error error => pure (.error error)
      | .ok (span,next) => tables := next; pure (.ok span)
    let decoded := do
      CompilerInstance.decode ctx tables (← body.input.payload.getObjVal? "constant_query_context")
    let callee ← match decoded with
      | .error error => pure (.error error)
      | .ok (callee,next) => tables := next; pure (.ok callee)
    let checks := do legacyLifecycleChecks ctx tables (← callee) body.input.payload
    let checks ← match checks with
      | .error error => pure (.error error)
      | .ok (checks,next) => tables := next; pure (.ok checks)
    entries := entries.push ⟨preamble,callee,checks⟩
  ⟨program.withCompilerTables tables,entries⟩

private def tablesSignature (program : LoweredProgram) :=
  (program.roots,program.instances,program.promoted,program.bundle.spans,
    program.bundle.definitions,program.bundle.typeConstants)

private def evidenceSignature (prepared : CompilerConstantQueries.Prepared) :=
  prepared.evidence.map fun item =>
    (item.site,item.query.fnInstance,item.query.original,item.query.normalized,
      item.query.span,item.query.value,item.sourcePayload,item.normalizedPayload)

private def lifecycleSignature (prepared : CompilerLifecycle.Prepared) :=
  prepared.entries.map fun entry => reprStr
    (entry.preamble,entry.callee,entry.checks.map fun checks => checks.map fun result =>
      result.map fun value =>
        (value.fnInstance,value.original,value.normalized,value.span,value.value))

private def constantsOutcomesEqual
    (left right : Except String CompilerConstantQueries.Prepared) : Bool :=
  match left,right with
  | .error leftError,.error rightError => leftError == rightError
  | .ok leftPrepared,.ok rightPrepared =>
    tablesSignature leftPrepared.program == tablesSignature rightPrepared.program &&
    evidenceSignature leftPrepared == evidenceSignature rightPrepared &&
    leftPrepared.obligations == rightPrepared.obligations
  | _,_ => false

private def replaceBodyPayload (program : LoweredProgram) (bodyIndex : Nat) (payload : Json) : LoweredProgram :=
  let bodies := program.bundle.bodies.mapIdx fun index old =>
    if index == bodyIndex then { old with input := { old.input with payload } } else old
  { program with bundle := { program.bundle with bodies } }

private def setField (j : Json) (key : String) (value : Json) : Json :=
  match j with
  | .obj fields => Json.mkObj ((fields.toList.filter (fun (name,_) => name != key) ++ [(key,value)]))
  | _ => j

private def eraseField (j : Json) (key : String) : Json :=
  match j with
  | .obj fields => Json.mkObj (fields.toList.filter (fun (name,_) => name != key))
  | _ => j

private partial def modifyPath (j : Json) (path : Array CompilerConstantQueries.PathElement)
    (change : Json → Json) : Json :=
  match path[0]? with
  | none => change j
  | some head =>
    match head with
    | .field name =>
      let child := (j.getObjVal? name).toOption.getD Json.null
      setField j name (modifyPath child (path.extract 1 path.size) change)
    | .index index =>
      match j with
      | .arr values => .arr (values.modify index fun child =>
          modifyPath child (path.extract 1 path.size) change)
      | _ => j

private def customSpan (span : Json) : Json :=
  setField (setField span "lo" (toJson (987654321 : Nat))) "hi" (toJson (987654322 : Nat))

private def setArrayIndex (j : Json) (index : Nat) (value : Json) : Json :=
  match j with
  | .arr values => .arr (values.set! index value)
  | _ => j

private def modifyAtSite (body : Json) (site : CompilerConstantQueries.Site)
    (change : Json → Json) : Except String Json := do
  let blocks ← array body "basic_blocks"
  let some blockIndex := blocks.findIdx? (fun block =>
      (natural block "block").toOption == some site.location.block)
    | throw "body is missing source basic block"
  let block := blocks[blockIndex]!
  let statements ← array block "statements"
  let envelope := if site.location.statementIndex == statements.size then
      (field block "terminator").toOption.getD Json.null
    else statements[site.location.statementIndex]?.getD Json.null
  let changed := modifyPath envelope site.path change
  let changedBlock := if site.location.statementIndex == statements.size then
      setField block "terminator" changed
    else setField block "statements"
      (setArrayIndex (.arr statements) site.location.statementIndex changed)
  pure (setField body "basic_blocks" (setArrayIndex (.arr blocks) blockIndex changedBlock))

private def spanAppendFailureProgram (program : LoweredProgram) :
    Except String (LoweredProgram × SourceSpanData) := do
  let mut firstSite : Option (Nat × CompilerConstantQueries.Site × Json) := none
  for bodyIndex in [:program.bundle.bodies.size] do
    if firstSite.isNone then
      if let some body := program.bundle.bodies[bodyIndex]? then
        if let .ok context := field body.input.payload "constant_query_context" then
          if let .ok normalization := field context "normalization" then
            if (normalization.getObjValAs? String "status").toOption == some "supported" then
              if let .ok _ := NormalizationBody.resolve normalization body.input.payload then
                if let .ok values := sourceConstants bodyIndex body.input.payload then
                  if let some (site,value) := values[0]? then
                    firstSite := some (bodyIndex,site,value)
  let some (bodyIndex,site,_) := firstSite
    | throw "mir_features fixture contains no evaluated constant source site"
  let some body := program.bundle.bodies[bodyIndex]? | throw "selected source body disappeared"
  let context ← field body.input.payload "constant_query_context"
  let normalization ← field context "normalization"
  let normalizedBody ← (NormalizationBody.resolve normalization body.input.payload).mapError
    (fun error => s!"resolve normalized body: {error}")
  let originalEnvelope ← (siteEnvelope body.input.payload site).mapError
    (fun error => s!"source envelope: {error}")
  let original ← (lookupPath originalEnvelope site.path).mapError
    (fun error => s!"lookup source constant: {error}")
  let span ← (field original "span").mapError (fun error => s!"source constant span: {error}")
  let uniqueSpan := customSpan span
  let uniqueSpanData ← match decodeCompilerValue uniqueSpan with
    | .ok (.sourceSpan decoded) => pure decoded
    | _ => throw s!"custom source span did not decode: {uniqueSpan.compress}"
  if program.bundle.spans.contains uniqueSpanData then
    throw "custom source span unexpectedly already occurs in the initial span table"
  let changedOriginal ← modifyAtSite body.input.payload site fun constant =>
    setField constant "span" uniqueSpan
  let changedNormalizedBody ← modifyAtSite normalizedBody site fun constant =>
    setField constant "span" uniqueSpan
  let changedNormalizedBody ← modifyAtSite changedNormalizedBody site fun constant =>
    let evaluated := (constant.getObjVal? "constant").toOption.getD Json.null
    setField constant "constant" (setField evaluated "status" (toJson "unsupported"))
  let changedNormalization := setField (eraseField normalization "body_ref") "body" changedNormalizedBody
  let changedContext := setField context "normalization" changedNormalization
  let payload := setField changedOriginal "constant_query_context" changedContext
  pure (replaceBodyPayload program bodyIndex payload, uniqueSpanData)

private def lifecycleBatchFailureProgram (program : LoweredProgram) :
    Except String (LoweredProgram × SourceSpanData) := do
  let mut found : Option (Nat × Nat × Json × Json × Json) := none
  for bodyIndex in [:program.bundle.bodies.size] do
    if found.isNone then
      if let some body := program.bundle.bodies[bodyIndex]? then
        let original := (body.input.payload.getObjVal? "required_consts").toOption.getD Json.null
        let context := (body.input.payload.getObjVal? "constant_query_context").toOption.getD Json.null
        let query := (context.getObjVal? "required_constant_checks").toOption.getD Json.null
        let originals := original.getArr?.toOption.getD #[]
        let checks := arrayOrEmpty ((query.getObjVal? "checks").toOption.getD Json.null)
        for index in [:min originals.size checks.size] do
          if found.isNone then
            let some _source := originals[index]? | continue
            let some check := checks[index]? | continue
            let result := (check.getObjVal? "result").toOption.getD Json.null
            if ((result.getObjVal? "status").bind Json.getStr?).toOption == some "supported" then
              found := some (bodyIndex,index,original,context,check)
  let some (bodyIndex,index,originals,context,check) := found
    | throw "mir_features fixture contains no supported required-constant check"
  let some body := program.bundle.bodies[bodyIndex]? | throw "selected lifecycle body disappeared"
  let originalArray := originals.getArr?.toOption.getD #[]
  let original := originalArray[index]!
  let sourceSpan ← field original "span"
  let uniqueSpan := customSpan sourceSpan
  let .sourceSpan uniqueSpanData ← decodeCompilerValue uniqueSpan
    | throw "custom lifecycle source span did not decode"
  if program.bundle.spans.contains uniqueSpanData then
    throw "custom lifecycle source span unexpectedly occurs in initial table"
  let original := setField original "span" uniqueSpan
  let originals := setArrayIndex originals index original
  let query := (context.getObjVal? "required_constant_checks").toOption.getD Json.null
  let checks := arrayOrEmpty ((query.getObjVal? "checks").toOption.getD Json.null)
  let result := (check.getObjVal? "result").toOption.getD Json.null
  let normalized := (result.getObjVal? "normalized_operand").toOption.getD Json.null
  let normalized := setField normalized "span" uniqueSpan
  let result := setField (setField result "normalized_operand" normalized) "value" Json.null
  let check := setField (setField check "result" result) "span" uniqueSpan
  let checks := setArrayIndex (.arr checks) index check
  let query := setField query "checks" checks
  let context := setField context "required_constant_checks" query
  let payload := setField (setField body.input.payload "required_consts" originals)
    "constant_query_context" context
  pure (replaceBodyPayload program bodyIndex payload,uniqueSpanData)

private def malformedBodyQueryProgram (program : LoweredProgram) : Except String LoweredProgram := do
  let some bodyIndex := (List.range program.bundle.bodies.size).find? fun index =>
      match program.bundle.bodies[index]? with
      | some body => (body.input.payload.getObjVal? "constant_query_context").isOk
      | none => false
    | throw "fixture contains no body constant query context"
  let some body := program.bundle.bodies[bodyIndex]? | throw "selected query body disappeared"
  let context := (body.input.payload.getObjVal? "constant_query_context").toOption.getD Json.null
  let malformedInstance := Json.mkObj [("kind",toJson "invalid_compiler_instance_kind")]
  let context := setField context "instance_kind" malformedInstance
  let payload := setField body.input.payload "constant_query_context" context
  pure (replaceBodyPayload program bodyIndex payload)

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected mir_features exporter JSON path")
  let text ← IO.FS.readFile path
  let decoded ← must (decodeJson text)
  let program ← must (lowerProgram decoded.document)

  let constants := CompilerConstantQueries.prepare program
  let legacyConstants := legacyConstantsPrepare program
  let .ok constantsPrepared := constants | throw (IO.userError "constant preparation failed")
  let .ok legacyConstantsPrepared := legacyConstants |
    throw (IO.userError "ordered-scan constant preparation failed")
  unless (tablesSignature constantsPrepared.program,evidenceSignature constantsPrepared,constantsPrepared.obligations) ==
      (tablesSignature legacyConstantsPrepared.program,evidenceSignature legacyConstantsPrepared,
        legacyConstantsPrepared.obligations) do
    throw (IO.userError "constant preparation differs from the ordered-scan reference")
  unless !constantsPrepared.evidence.isEmpty do
    throw (IO.userError "mir_features fixture did not exercise constant query evidence")
  let lifecycle := CompilerLifecycle.prepare program
  let legacyLifecycle := legacyLifecyclePrepare program
  unless tablesSignature lifecycle.program == tablesSignature legacyLifecycle.program &&
      lifecycleSignature lifecycle == lifecycleSignature legacyLifecycle do
    throw (IO.userError "lifecycle preparation differs from the ordered-scan reference")

  let (failed,uniqueSpan) ← must (spanAppendFailureProgram program)
  let failedFast ← must (CompilerConstantQueries.prepare failed)
  let failedScan ← must (legacyConstantsPrepare failed)
  unless tablesSignature failedFast.program == tablesSignature failedScan.program &&
      evidenceSignature failedFast == evidenceSignature failedScan &&
      failedFast.obligations == failedScan.obligations do
    throw (IO.userError "constant evidence failure changed interner rollback or obligation order")
  if failedFast.program.bundle.spans.contains uniqueSpan then
    throw (IO.userError "failed constant evidence retained a span appended before the failure")

  let (batchFailed,batchSpan) ← must (lifecycleBatchFailureProgram program)
  let batchFast := CompilerLifecycle.prepare batchFailed
  let batchScan := legacyLifecyclePrepare batchFailed
  unless tablesSignature batchFast.program == tablesSignature batchScan.program &&
      lifecycleSignature batchFast == lifecycleSignature batchScan do
    throw (IO.userError "lifecycle failed batch differs from ordered-scan reference")
  if batchFast.program.bundle.spans.contains batchSpan then
    throw (IO.userError "failed lifecycle batch retained a span appended before the failure")

  let malformed ← must (malformedBodyQueryProgram program)
  unless constantsOutcomesEqual (CompilerConstantQueries.prepare malformed)
      (legacyConstantsPrepare malformed) do
    throw (IO.userError "malformed body-query decoder outcome differs from ordered-scan reference")
  unless lifecycleSignature (CompilerLifecycle.prepare malformed) ==
      lifecycleSignature (legacyLifecyclePrepare malformed) do
    throw (IO.userError "malformed lifecycle body-query decoder outcome differs from ordered-scan reference")
  IO.println s!"constant/lifecycle preparation matches ordered-scan reference ({program.bundle.bodies.size} bodies; {constantsPrepared.evidence.size} constants)"
