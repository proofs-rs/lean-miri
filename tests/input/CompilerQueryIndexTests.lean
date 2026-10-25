import Miri.Input
import Miri.Interpreter.FunctionCalls

/-! Demand-level compatibility regression for the prepared compiler query
indices. The input is a retained producer export, supplied as the first CLI
argument. Every case decodes, lowers, and prepares the mutated export through
the public path; no Prepared provider or index is manually assembled. -/
open Lean Miri Miri.ABI Miri.Input Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def field (j : Json) (key : String) : Except String Json := j.getObjVal? key

private def setField (j : Json) (key : String) (value : Json) : Except String Json := do
  match j with
  | .obj fields =>
    let retained := fields.toList.filter fun entry => entry.1 != key
    pure (Json.mkObj ((key, value) :: retained))
  | _ => throw "expected object while setting a test field"

private def array (j : Json) : Except String (Array Json) := j.getArr?

private def appendRootArray (raw : Json) (key : String) (extra : Json) : Except String Json := do
  let values ← array (← field raw key)
  setField raw key (.arr (values.push extra))

private def appendSignature (raw row : Json) : Except String Json := do
  let facts ← field raw "compiler_function_facts"
  let rows ← array (← field facts "helper_signatures")
  let facts ← setField facts "helper_signatures" (.arr (rows.push row))
  setField raw "compiler_function_facts" facts

private def replaceSignatureAt (raw : Json) (index : Nat) (row : Json) : Except String Json := do
  let facts ← field raw "compiler_function_facts"
  let rows ← array (← field facts "helper_signatures")
  if index ≥ rows.size then throw "signature test row out of range"
  let rows := rows.set! index row
  let facts ← setField facts "helper_signatures" (.arr rows)
  setField raw "compiler_function_facts" facts

private def replaceCovarianceAt (raw : Json) (index : Nat) (row : Json) : Except String Json := do
  let rows ← array (← field raw "compiler_covariance_queries")
  if index ≥ rows.size then throw "covariance test row out of range"
  setField raw "compiler_covariance_queries" (.arr (rows.set! index row))

private def prepared (raw : Json) : IO CompilerProviders.Prepared := do
  let decoded ← must (decodeJson raw.compress)
  let program ← must (lowerProgram decoded.document)
  must (CompilerProviders.prepare program)

private def resultText [Repr α] (result : Except String α) : String :=
  match result with
  | .ok value => "ok: " ++ reprStr value
  | .error error => "error: " ++ error

private def legacyCovariance (p : CompilerProviders.Prepared) (source target : MIR.TyId) :
    Except String Bool := do
  if source == target then return true
  let entries ← (← p.program.input.raw.getObjVal? "compiler_covariance_queries").getArr?
  let mut found := none
  for entry in entries do
    let a ← (← entry.getObjVal? "source_type").getObjValAs? Nat "type_id"
    let b ← (← entry.getObjVal? "target_type").getObjValAs? Nat "type_id"
    if a == source && b == target then
      unless (← entry.getObjValAs? String "typing_env") == "fully_monomorphized" &&
          (← entry.getObjValAs? String "variance") == "covariant" do
        throw s!"compiler covariance query key/environment mismatch (source={source}, target={target})"
      unless (← entry.getObjValAs? String "status") == "supported" do
        throw s!"compiler covariance query unresolved (source={source}, target={target})"
      let value ← entry.getObjValAs? Bool "value"
      if let some old := found then
        unless old == value do
          throw s!"conflicting compiler covariance query results (source={source}, target={target})"
      found := some value
  let some value := found |
    throw s!"missing exact rustc covariance relation query (source={source}, target={target})"
  pure value

private def typeRef (p : CompilerProviders.Prepared) (source : Json) : Except String MIR.TyId := do
  let id ← source.getObjValAs? Nat "type_id"
  let _ ← p.runtime.node id |>.mapError toString
  pure id

private def requestOf (p : CompilerProviders.Prepared) (record : Json) :
    Except String (FunctionCalls.SignatureRequest ABI.ExternAbi) := do
  unless (← record.getObjValAs? String "typing_env") == "fully_monomorphized" do
    throw "authentic helper signature had an unexpected typing environment"
  let signature ← record.getObjVal? "signature"
  let inputs ← (← (← signature.getObjVal? "inputs").getArr?).mapM (typeRef p)
  let output ← typeRef p (← signature.getObjVal? "output")
  let abi ← CompilerExternAbi.decode (← signature.getObjVal? "abi")
  let safety ← signature.getObjVal? "safety"
  let safety ← match ← safety.getObjValAs? String "kind" with
    | "safe" => pure MIR.Safety.Safe
    | "unsafe" => pure MIR.Safety.Unsafe
    | _ => throw "unknown authentic helper safety"
  let cVariadic ← signature.getObjValAs? Bool "c_variadic"
  let splatted ← record.getObjValAs? Bool "splatted"
  pure ⟨inputs, output, abi, safety, cVariadic, splatted⟩

private def legacySignatureAbi (p : CompilerProviders.Prepared)
    (request : FunctionCalls.SignatureRequest ABI.ExternAbi) : Except String (FnAbi MIR.TyId) := do
  let records ← (← (← p.program.input.raw.getObjVal? "compiler_function_facts").getObjVal? "helper_signatures").getArr?
  let mut found : Option Json := none
  for record in records do
    unless (← record.getObjValAs? String "typing_env") == "fully_monomorphized" do
      throw "helper signature compiler typing environment mismatch"
    let signature ← record.getObjVal? "signature"
    let inputs ← (← (← signature.getObjVal? "inputs").getArr?).mapM (typeRef p)
    let output ← typeRef p (← signature.getObjVal? "output")
    let abi ← CompilerExternAbi.decode (← signature.getObjVal? "abi")
    let safety ← signature.getObjVal? "safety"
    unless (← safety.getObjValAs? String "status") == "supported" do
      throw "helper safety metadata unsupported"
    let safety ← match ← safety.getObjValAs? String "kind" with
      | "safe" => pure MIR.Safety.Safe
      | "unsafe" => pure MIR.Safety.Unsafe
      | _ => throw "unknown helper signature safety"
    let variadic ← signature.getObjValAs? Bool "c_variadic"
    let splatted ← record.getObjValAs? Bool "splatted"
    if inputs == request.inputs && output == request.output && abi == request.abi &&
        safety == request.safety && variadic == request.cVariadic && splatted == request.splatted then
      let value ← record.getObjVal? "abi_query"
      if let some previous := found then
        unless value == previous do throw "conflicting exact helper signature ABI evidence"
      found := some value
  let some result := found | throw s!"missing exact compiler dummy-signature ABI query: inputs={reprStr request.inputs}, output={request.output}, abi={reprStr request.abi}, safety={reprStr request.safety}, c_variadic={request.cVariadic}, splatted={request.splatted}"
  unless (← result.getObjValAs? String "status") == "supported" do
    throw s!"compiler dummy-signature ABI query failed: {result.compress}"
  CallResolution.functionAbi p.runtime (← decodeCompilerFunctionAbi (← result.getObjVal? "value"))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "authentic producer export path required")
  let raw ← must (Json.parse (← IO.FS.readFile path))
  let raw ← must (SharedPayloads.resolveCatalog raw)
  let raw ← must (setField raw "shared_payloads" (Json.mkObj [
    ("schema_version", toJson (2 : Nat)), ("nodes", toJson (#[] : Array Json))]))
  let baseline ← prepared raw

  let covarianceTable ← must (field raw "compiler_covariance_queries")
  let covarianceRows ← must (array covarianceTable)
  let covarianceIndex := (covarianceRows.toList.zipIdx.find? fun (row, _) =>
    (row.getObjValAs? Bool "value" |>.toOption) == some false).map Prod.snd |>.getD 0
  let covarianceRow ← match covarianceRows[covarianceIndex]? with
    | some row => pure row
    | none => throw (IO.userError "authentic producer export has no covariance query")
  let sourceRow ← must (field covarianceRow "source_type")
  let targetRow ← must (field covarianceRow "target_type")
  let source ← must (sourceRow.getObjValAs? Nat "type_id")
  let target ← must (targetRow.getObjValAs? Nat "type_id")
  let expected ← must (covarianceRow.getObjValAs? Bool "value")
  let actual ← must (CompilerCovariance.relationWithIndex baseline.covarianceIndex source target)
  check (actual == expected) "exact producer covariance answer changed"
  let legacyActual := legacyCovariance baseline source target
  check (resultText (.ok actual) == resultText legacyActual)
    "genuine exact covariance differs from prior scan"
  let reflexive ← must (CompilerCovariance.relationWithIndex baseline.covarianceIndex source source)
  check reflexive "reflexive covariance query did not bypass catalog demand"
  let covarianceRowsJson ← must (field raw "compiler_covariance_queries")
  let covarianceRows ← must (array covarianceRowsJson)
  let secondCovarianceRow ← match covarianceRows[1]? with
    | some row => pure row
    | none => throw (IO.userError "authentic producer export has fewer than two covariance queries")
  let thirdCovarianceRow ← match covarianceRows[2]? with
    | some row => pure row
    | none => throw (IO.userError "authentic producer export has fewer than three covariance queries")
  let conflictingCovarianceRow ← must (setField covarianceRow "value" (toJson (!expected)))
  let covarianceMutated ← must (replaceCovarianceAt raw covarianceIndex conflictingCovarianceRow)
  let covarianceMutated ← must (appendRootArray covarianceMutated "compiler_covariance_queries" covarianceRow)
  let unsupportedCovarianceRow ← must (setField secondCovarianceRow "status" (toJson "unsupported"))
  let covarianceMutated ← must (replaceCovarianceAt covarianceMutated 1 unsupportedCovarianceRow)
  let malformedUnrelatedCovariance ← must (setField thirdCovarianceRow "status" (toJson "malformed-but-unrelated"))
  let covarianceMutated ← must (replaceCovarianceAt covarianceMutated 2 malformedUnrelatedCovariance)
  let covarianceMutated ← must (appendRootArray covarianceMutated "compiler_covariance_queries" Json.null)
  let covariancePrepared ← prepared covarianceMutated
  check (CompilerCovariance.relationWithIndex covariancePrepared.covarianceIndex source source == .ok true)
    "reflexive covariance query did not bypass the catalog's malformed row"
  let conflictResult := CompilerCovariance.relationWithIndex covariancePrepared.covarianceIndex source target
  check (!conflictResult.isOk) "conflicting exact covariance duplicate was accepted"
  check (resultText conflictResult == resultText (legacyCovariance covariancePrepared source target))
    "conflicting exact covariance duplicate changed old scan result/error"
  let secondSourceRow ← must (field secondCovarianceRow "source_type")
  let secondTargetRow ← must (field secondCovarianceRow "target_type")
  let secondSource ← must (secondSourceRow.getObjValAs? Nat "type_id")
  let secondTarget ← must (secondTargetRow.getObjValAs? Nat "type_id")
  let unsupportedResult := CompilerCovariance.relationWithIndex covariancePrepared.covarianceIndex secondSource secondTarget
  check (resultText unsupportedResult == resultText (legacyCovariance covariancePrepared secondSource secondTarget))
    "unsupported exact covariance row changed old scan result/error"
  let missingCovariance := CompilerCovariance.relationWithIndex covariancePrepared.covarianceIndex 999999998 999999999
  check (resultText missingCovariance == resultText (legacyCovariance covariancePrepared 999999998 999999999))
    "missing exact covariance diagnostic changed old scan result/error"

  let facts ← must (field raw "compiler_function_facts")
  let signatures ← must (field facts "helper_signatures")
  let signatureRows ← must (array signatures)
  let signatureRow ← match signatureRows[0]? with
    | some row => pure row
    | none => throw (IO.userError "authentic producer export has no helper signatures")
  let request ← must (requestOf baseline signatureRow)
  let genuineCurrent := CompilerSignatureAbi.queryWithIndex baseline.runtime baseline.signatureAbiIndex request
  let genuineLegacy := legacySignatureAbi baseline request
  check (resultText genuineCurrent == resultText genuineLegacy)
    "genuine exact signature ABI differs from prior scan"
  let repeatedCurrent := CompilerSignatureAbi.queryWithIndex baseline.runtime baseline.signatureAbiIndex request
  check (resultText repeatedCurrent == resultText genuineLegacy)
    "repeated successful signature ABI request differs from prior scan"

  -- Synthetic duplicate: the last row is byte-for-byte identical, so the
  -- index must retain last-row selection while agreeing with the old scan.
  let identicalDuplicateRaw ← must (appendSignature raw signatureRow)
  let identicalDuplicatePrepared ← prepared identicalDuplicateRaw
  let duplicateCurrent := CompilerSignatureAbi.queryWithIndex
    identicalDuplicatePrepared.runtime identicalDuplicatePrepared.signatureAbiIndex request
  let duplicateLegacy := legacySignatureAbi identicalDuplicatePrepared request
  check (resultText duplicateCurrent == resultText duplicateLegacy)
    "identical duplicate signature ABI differs from prior scan"

  -- Exercise every genuine catalog key where possible. This also covers
  -- equal input/output types distinguished by ABI, safety, variadic, or
  -- splatted fields when the producer export contains such pairs.
  let mut sameShapeDistinctKeys := 0
  let mut requests : Array (FunctionCalls.SignatureRequest ABI.ExternAbi) := #[]
  for row in signatureRows do
    let rowRequest ← must (requestOf baseline row)
    let indexed := CompilerSignatureAbi.queryWithIndex baseline.runtime baseline.signatureAbiIndex rowRequest
    let scanned := legacySignatureAbi baseline rowRequest
    check (resultText indexed == resultText scanned)
      "genuine signature catalog row differs from prior scan"
    for previous in requests do
      if previous.inputs == rowRequest.inputs && previous.output == rowRequest.output &&
          (previous.abi != rowRequest.abi || previous.safety != rowRequest.safety ||
           previous.cVariadic != rowRequest.cVariadic || previous.splatted != rowRequest.splatted) then
        sameShapeDistinctKeys := sameShapeDistinctKeys + 1
    requests := requests.push rowRequest
  IO.println s!"genuine same-input/output distinct signature-key pairs: {sameShapeDistinctKeys}"
  let secondSignatureRow ← match signatureRows[1]? with
    | some row => pure row
    | none => throw (IO.userError "authentic producer export has fewer than two helper signatures")
  let thirdSignatureRow ← match signatureRows[2]? with
    | some row => pure row
    | none => throw (IO.userError "authentic producer export has fewer than three helper signatures")
  let secondRequest ← must (requestOf baseline secondSignatureRow)
  let thirdRequest ← must (requestOf baseline thirdSignatureRow)
  let signatureMutated ← must (appendSignature raw signatureRow)
  let facts ← must (field signatureMutated "compiler_function_facts")
  let currentSignatures ← must (field facts "helper_signatures")
  let currentRows ← must (array currentSignatures)
  let secondQuery ← must (field (currentRows[1]!) "abi_query")
  let secondUnsupported ← must (setField secondQuery "status" (toJson "unsupported"))
  let secondRow ← must (setField (currentRows[1]!) "abi_query" secondUnsupported)
  let signatureMutated ← must (replaceSignatureAt signatureMutated 1 secondRow)
  let facts ← must (field signatureMutated "compiler_function_facts")
  let currentSignatures ← must (field facts "helper_signatures")
  let currentRows ← must (array currentSignatures)
  let duplicateUnsupported := currentRows[1]!
  let signatureMutated ← must (appendSignature signatureMutated duplicateUnsupported)
  let facts ← must (field signatureMutated "compiler_function_facts")
  let currentSignatures ← must (field facts "helper_signatures")
  let currentRows ← must (array currentSignatures)
  let thirdBadQuery ← must (setField (currentRows[2]!) "abi_query" (toJson "malformed unrelated result"))
  let signatureMutated ← must (replaceSignatureAt signatureMutated 2 thirdBadQuery)
  let conflictingSignatureRow ← must (setField signatureRow "abi_query" (Json.mkObj [("status", toJson "different")] ))
  let signatureMutated ← must (appendSignature signatureMutated conflictingSignatureRow)
  let signaturePrepared ← prepared signatureMutated
  let currentFirst := CompilerSignatureAbi.queryWithIndex signaturePrepared.runtime signaturePrepared.signatureAbiIndex request
  let legacyFirst := legacySignatureAbi signaturePrepared request
  check (resultText currentFirst == resultText legacyFirst)
    s!"conflicting exact signature duplicate changed old scan result/error: current={resultText currentFirst}; legacy={resultText legacyFirst}"
  let currentSecond := CompilerSignatureAbi.queryWithIndex signaturePrepared.runtime signaturePrepared.signatureAbiIndex secondRequest
  let legacySecond := legacySignatureAbi signaturePrepared secondRequest
  check (resultText currentSecond == resultText legacySecond)
    s!"unsupported exact signature row changed old scan result/error: current={resultText currentSecond}; legacy={resultText legacySecond}"
  let currentThird := CompilerSignatureAbi.queryWithIndex signaturePrepared.runtime signaturePrepared.signatureAbiIndex thirdRequest
  let legacyThird := legacySignatureAbi signaturePrepared thirdRequest
  check (resultText currentThird == resultText legacyThird)
    s!"malformed unrelated signature row changed old scan result/error: current={resultText currentThird}; legacy={resultText legacyThird}"
  let missingRequest := { request with output := 999999999 }
  let currentMissing := CompilerSignatureAbi.queryWithIndex signaturePrepared.runtime signaturePrepared.signatureAbiIndex missingRequest
  let legacyMissing := legacySignatureAbi signaturePrepared missingRequest
  check (resultText currentMissing == resultText legacyMissing)
    s!"missing exact signature row changed old scan result/error: current={resultText currentMissing}; legacy={resultText legacyMissing}"
  IO.println "prepared compiler query indices preserve source scan results and diagnostics on authentic export mutations"

/- The type indices carry their raw/runtime source values in the type. This
expected diagnostic makes accidental cache rebinding fail the normal test
module if an index can be supplied for a distinct source value. -/
/-- error: Type mismatch -/
#guard_msgs (error, substring := true) in
#check (CompilerQueryIndices.covariance Json.null : CompilerQueryIndices.Covariance (Json.str "changed"))

/-- error: Type mismatch -/
#guard_msgs (error, substring := true) in
example (runtime₁ runtime₂ : RuntimeMetadata) (raw : Json) :
    CompilerQueryIndices.SignatureAbi runtime₂ raw :=
  CompilerQueryIndices.signatureAbi runtime₁ raw
