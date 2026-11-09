import Miri.Input
import Miri.Interpreter.FunctionCalls

open Lean Miri Miri.ABI Miri.Input Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def requestOf (row : Catalog.HelperSignature) :
    FunctionCalls.SignatureRequest ABI.ExternAbi :=
  ⟨row.signature.inputs, row.signature.output, row.signature.abi,
    row.signature.safety, row.signature.cVariadic, row.splatted⟩

private def setField (value : Json) (key : String) (replacement : Json) : Except String Json := do
  pure (Json.mkObj ((key, replacement) :: (← value.getObj?).toList.filter (·.1 != key)))

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "producer export path required")
  let text ← IO.FS.readFile path
  let decoded ← must (decodeJson text)
  let program ← must (lowerProgram decoded.document)
  let baseline ← must (CompilerProviders.prepare program)
  let queries := program.input.queries
  let some covariance := queries.covariance.find? (fun row => row.sourceType != row.targetType) |
    throw (IO.userError "fixture has no non-reflexive covariance query")
  for row in queries.covariance do
    let actual ← must (CompilerCovariance.relationWithIndex baseline.covarianceIndex row.sourceType row.targetType)
    check (actual == (row.sourceType == row.targetType || row.value)) "producer covariance answer changed"
  let conflicting := CompilerQueryIndices.covariance
    (queries.covariance.push {covariance with value := !covariance.value})
  check (!(CompilerCovariance.relationWithIndex conflicting covariance.sourceType covariance.targetType).isOk)
    "conflicting covariance duplicate was accepted"
  check (CompilerCovariance.relationWithIndex conflicting covariance.sourceType covariance.sourceType == .ok true)
    "reflexive covariance did not bypass catalog demand"
  check (!(CompilerCovariance.relationWithIndex baseline.covarianceIndex 999999998 999999999).isOk)
    "missing covariance key was accepted"
  let signatures := queries.functionFacts.helperSignatures
  let some first := signatures[0]? | throw (IO.userError "fixture has no helper signatures")
  for row in signatures do
    let actual ← must (CompilerSignatureAbi.queryWithIndex baseline.runtime baseline.signatureAbiIndex (requestOf row))
    let expected ← must (CallResolution.functionAbiId baseline.runtime row.abiId)
    check (decide (actual = expected)) "helper signature resolved to a different ABI"
  let duplicate := CompilerQueryIndices.signatureAbi (signatures.push first)
  let actual ← must (CompilerSignatureAbi.queryWithIndex baseline.runtime duplicate (requestOf first))
  let expected ← must (CallResolution.functionAbiId baseline.runtime first.abiId)
  check (decide (actual = expected)) "identical helper signature duplicate changed ABI"
  let conflicting := CompilerQueryIndices.signatureAbi
    (signatures.push {first with abiId := first.abiId + 1})
  check (!(CompilerSignatureAbi.queryWithIndex baseline.runtime conflicting (requestOf first)).isOk)
    "conflicting helper signature duplicate was accepted"
  let missing := { requestOf first with output := 999999999 }
  check (!(CompilerSignatureAbi.queryWithIndex baseline.runtime baseline.signatureAbiIndex missing).isOk)
    "missing helper signature key was accepted"
  let keys := signatures.map fun row => CompilerQueryIndices.signatureRequestKey row.signature.inputs
    row.signature.output row.signature.abi row.signature.safety row.signature.cVariadic row.splatted
  check ((CompilerQueryIndices.signatureRequestKey first.signature.inputs first.signature.output
    first.signature.abi first.signature.safety first.signature.cVariadic (!first.splatted)) != keys[0]!)
    "splatted flag was omitted from the signature key"
  let raw ← must (Json.parse text)
  let badCovariance ← must (setField raw "compiler_covariance_queries" (.arr #[.null]))
  check (!(decodeJson badCovariance.compress).isOk) "malformed covariance row passed import"
  let facts ← must (raw.getObjVal? "compiler_function_facts")
  let badFacts ← must (setField facts "helper_signatures" (.arr #[.null]))
  let badSignatures ← must (setField raw "compiler_function_facts" badFacts)
  check (!(decodeJson badSignatures.compress).isOk) "malformed helper signature row passed import"
  IO.println "typed query indices preserve exact keys, ABI references, duplicate conflicts and missing-key failures"
