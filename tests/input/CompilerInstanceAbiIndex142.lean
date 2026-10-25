import Miri.Input

open Lean Miri.Input Miri.ABI Miri.Interpreter

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

/-- Independent source-order implementation retained from the pre-index API. -/
private def oldLinear (entries : Array CompilerInstanceAbi.Entry)
    (callee : CallInstance) (extra : Array Miri.MIR.TyId) :
    Except String (FnAbi Miri.MIR.TyId) := do
  let some entry := entries.find? (fun entry => entry.callee == callee && entry.extra == extra)
    | throw "missing exact full-instance/extra-argument FnAbi query"
  entry.result

private def field (json : Json) (name : String) : Except String Json :=
  json.getObjVal? name

private def setField (json : Json) (name : String) (value : Json) : Except String Json := do
  match json with
  | .obj fields =>
    let retained := fields.toList.filter fun pair => pair.1 != name
    pure (Json.mkObj ((name, value) :: retained))
  | _ => throw "expected JSON object in adversarial test"

private def abiRows (raw : Json) : Except String (Array Json) := do
  (← field raw "compiler_instance_abis").getArr?

private def withAbiRows (raw : Json) (rows : Array Json) : Except String Json :=
  setField raw "compiler_instance_abis" (.arr rows)

private def appendAbiRows (raw : Json) (added : Array Json) : Except String Json := do
  let rows ← abiRows raw
  withAbiRows raw (rows ++ added)

private def replaceAbiRow (raw old replacement : Json) : Except String Json := do
  let rows ← abiRows raw
  let some index := rows.findIdx? (· == old) | throw "ABI row to replace was absent"
  withAbiRows raw (rows.set! index replacement)

private def rewriteGenericType (row : Json) (typeId : Nat) : Except String Json := do
  let args ← (← field row "generic_args").getArr?
  let mut rewritten := false
  let mut newArgs := #[]
  for arg in args do
    if rewritten || (← arg.getObjValAs? String "kind") != "type" then
      newArgs := newArgs.push arg
    else
      rewritten := true
      let value ← field arg "value"
      let value ← setField value "type_id" (toJson typeId)
      newArgs := newArgs.push (← setField arg "value" value)
  unless rewritten do throw "fixture did not contain a type generic argument"
  setField row "generic_args" (.arr newArgs)

private def withQuery (row query : Json) : Except String Json :=
  setField row "abi_query" query

private def withQueryValue (row value : Json) : Except String Json := do
  let query ← field row "abi_query"
  withQuery row (← setField query "value" value)

private def withQueryStatus (row : Json) (status reason : String) : Except String Json := do
  let query ← field row "abi_query"
  let query ← setField query "status" (.str status)
  let query ← setField query "reason" (.str reason)
  withQuery row query

private def prepareRaw (raw : Json) : IO (Except String CompilerInstanceAbi.Prepared) := do
  let decoded ← match decodeJson raw.compress with
    | .ok decoded => pure decoded
    | .error error => throw (IO.userError error)
  let doc := decoded.document
  let runtime ← match RuntimeMetadata.ofDocument doc with
    | .ok runtime => pure runtime
    | .error error => throw (IO.userError (toString error))
  let program ← match lowerProgram doc with
    | .ok program => pure program
    | .error error => throw (IO.userError error)
  pure (CompilerInstanceAbi.prepare runtime program)

private def comparePrepared (prepared : CompilerInstanceAbi.Prepared) : IO Unit := do
  for entry in prepared.entries do
    check (CompilerInstanceAbi.abiOfInstance prepared entry.callee entry.extra ==
      oldLinear prepared.entries entry.callee entry.extra)
      s!"synthetic indexed result differs from old linear scan for {reprStr entry.callee}, extra={entry.extra}"

private def expectPrepareError (raw : Json) (expected : String) : IO Unit := do
  let result ← prepareRaw raw
  match result with
  | .error error => check (error == expected) s!"expected prepare error '{expected}', received '{error}'"
  | .ok _ => throw (IO.userError s!"expected prepare to fail with '{expected}'")

def main (args : List String) : IO Unit := do
  let some path := args.head? | throw (IO.userError "expected unmodified genuine producer JSON")
  let text ← IO.FS.readFile path
  let raw ← match Json.parse text with
    | .ok raw => pure raw
    | .error error => throw (IO.userError error)
  let raw ← must (SharedPayloads.resolveCatalog raw)
  let raw ← must (setField raw "shared_payloads" (Json.mkObj [
    ("schema_version", toJson (2 : Nat)), ("nodes", toJson (#[] : Array Json))]))
  let decoded ← must (decodeJson text)
  let doc := decoded.document
  let runtime ← must ((RuntimeMetadata.ofDocument doc).mapError toString)
  let program ← must (lowerProgram doc)
  let prepared ← must (CompilerInstanceAbi.prepare runtime program)
  for entry in prepared.entries do
    let indexed := CompilerInstanceAbi.abiOfInstance prepared entry.callee entry.extra
    let linear := oldLinear prepared.entries entry.callee entry.extra
    check (indexed == linear)
      s!"indexed result differs from old linear scan for {reprStr entry.callee}, extra={entry.extra}"
  let missing : CallInstance := ⟨.Item 0, #[]⟩
  let indexedMissing := CompilerInstanceAbi.abiOfInstance prepared missing #[]
  let linearMissing := oldLinear prepared.entries missing #[]
  check (indexedMissing == linearMissing) "missing-key error differs from old linear scan"
  let manual : CompilerInstanceAbi.Prepared := ⟨program, prepared.entries, none⟩
  for entry in manual.entries do
    let fallback := CompilerInstanceAbi.abiOfInstance manual entry.callee entry.extra
    let linear := oldLinear manual.entries entry.callee entry.extra
    check (fallback == linear)
      s!"manual Prepared fallback differs from old linear scan for {reprStr entry.callee}"
  IO.println s!"genuine source133 root_u32: prepared {prepared.entries.size} unique exact ABI entries; indexed and manual fallback outcomes match full linear scan for all keys plus missing key"

  -- Synthetic-only copies exercise key dimensions the genuine source export
  -- does not provide. The unmodified fixture above remains the provenance base.
  let rows ← must (abiRows raw)
  let some reify := rows.find? (fun row =>
    ((field row "instance_kind").bind (field · "shim_kind")).toOption == some (.str "reify"))
    | throw (IO.userError "fixture lacks a genuine reify record")
  let some genericTypeRow := rows.find? (fun row =>
    (((field row "generic_args").bind Json.getArr?).toOption.getD #[]).any fun arg =>
      ((arg.getObjValAs? String "kind").toOption == some "type"))
    | throw (IO.userError "fixture lacks a type generic argument")
  let some genericType := doc.types[0]? | throw (IO.userError "fixture has no compiler type")
  let genericVariant ← must (rewriteGenericType genericTypeRow genericType.id)
  let instanceKind ← must (field reify "instance_kind")
  let changedReason ← must (setField instanceKind "reason" (.str "function_pointer"))
  let reasonVariant ← must (setField reify "instance_kind" changedReason)
  let shimKind ← must (setField instanceKind "shim_kind" (.str "fn_pointer"))
  let shimKind ← must (setField shimKind "function_type" (Json.mkObj [("type_id", toJson genericType.id)]))
  let fnPointerVariant ← must (setField reify "instance_kind" shimKind)
  let extraVariant ← must (setField reify "extra_argument_types"
    (.arr #[Json.mkObj [("type_id", toJson genericType.id)]]))
  let extendedRaw ← must (appendAbiRows raw #[reasonVariant, fnPointerVariant, genericVariant, extraVariant])
  let extended ← match ← prepareRaw extendedRaw with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"synthetic distinct-key rows failed preparation: {error}")
  check (extended.entries.size == prepared.entries.size + 4)
    "synthetic shim/generic/extra variants did not remain distinct full keys"
  comparePrepared extended
  IO.println s!"synthetic distinct keys: preserved reify payload, shim kind, generic argument, and nonempty extra argument; all {extended.entries.size} outcomes match linear scan"

  let duplicateRaw ← must (appendAbiRows raw #[reify])
  let duplicate ← match ← prepareRaw duplicateRaw with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"identical duplicate failed preparation: {error}")
  check (duplicate.entries.size == prepared.entries.size) "identical duplicate was not coalesced"
  comparePrepared duplicate

  let query ← must (field reify "abi_query")
  let value ← must (field query "value")
  let canUnwind ← must (value.getObjValAs? Bool "can_unwind")
  let changedValue ← must (setField value "can_unwind" (.bool (!canUnwind)))
  let conflictingSuccess ← must (withQueryValue reify changedValue)
  let successConflictRaw ← must (appendAbiRows raw #[conflictingSuccess])
  expectPrepareError successConflictRaw "conflicting exact instance ABI evidence"

  let failureOne ← must (withQueryStatus reify "unavailable" "synthetic failure one")
  let failureTwo ← must (withQueryStatus reify "unavailable" "synthetic failure two")
  let failureBase ← must (replaceAbiRow raw reify failureOne)
  let sameFailureRaw ← must (appendAbiRows failureBase #[failureOne])
  let failedPrepared ← match ← prepareRaw sameFailureRaw with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"same failed duplicate did not coalesce: {error}")
  comparePrepared failedPrepared
  let failedConflictRaw ← must (appendAbiRows failureBase #[failureTwo])
  expectPrepareError failedConflictRaw "conflicting failed instance ABI evidence"
  let statusConflictRaw ← must (appendAbiRows raw #[failureOne])
  expectPrepareError statusConflictRaw "conflicting instance ABI query status"
  IO.println "synthetic duplicates/status: same evidence coalesces; conflicting success, conflicting failures, and mixed status retain exact prior errors"
