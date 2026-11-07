import Miri.Input.Decoder

open Lean Miri.Input ReferenceValidation

private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)

private def source (id : Nat) : Json := Json.mkObj [
  ("types", toJson #[Json.mkObj [("type_id",toJson (1 : Nat))],
    Json.mkObj [("type_id",toJson (0 : Nat))]]),
  ("allocations",toJson (#[] : Array Json)),
  ("instances",toJson (#[] : Array Json)),
  ("value",Json.mkObj [("type_id",toJson id)])]

private def bodySource (localIndex target : Nat) : Json := Json.mkObj [
  ("types",toJson (#[] : Array Json)), ("allocations",toJson (#[] : Array Json)),
  ("instances",toJson (#[] : Array Json)),
  ("bodies",toJson #[Json.mkObj [
    ("locals",toJson #[Json.mkObj [("local",toJson (0 : Nat))]]),
    ("basic_blocks",toJson #[Json.mkObj [("block",toJson (0 : Nat)),
      ("statements",toJson #[Json.mkObj [("kind",Json.mkObj [("local",toJson localIndex)])]]),
      ("terminator",Json.mkObj [("kind",Json.mkObj [("variant",toJson ("Goto" : String)),
        ("target",toJson target)])])]])]])]

private def checkBodyBounds : IO Unit := do
  let checked ← must (validate (bodySource 0 0))
  let some body := checked.summary.bodies[0]? | throw (IO.userError "body scope was lost")
  unless body.locals.size == 1 && !body.blocks.isEmpty && body.blocks.all (·.2.val == 0) do
    throw (IO.userError "local/block references were lost")
  for (input, expected) in [
      (bodySource 1 0, "$.bodies[0].basic_blocks[0].statements[0].kind.local: local 1 is out of range (locals=1)"),
      (bodySource 0 1, "$.bodies[0].basic_blocks[0].terminator.kind.target: basic block 1 is out of range (blocks=1)")] do
    match validate input with
    | .ok _ => throw (IO.userError "out-of-range body reference was accepted")
    | .error reason =>
      unless reason == expected do throw (IO.userError s!"body diagnostic differs: {reason}")

private def setField (value : Json) (key : String) (replacement : Json) : Json :=
  match value with
  | .obj fields => Json.mkObj ((key,replacement) :: fields.toList.filter (·.1 != key))
  | _ => value

private def checkOptionalEdges : IO Unit := do
  for (variant, optional, required) in [("Drop", "async_drop", "target"), ("Yield", "drop", "resume")] do
    let root := bodySource 0 0
    let bodies ← must ((← must (root.getObjVal? "bodies")).getArr?)
    let blocks ← must ((← must (bodies[0]!.getObjVal? "basic_blocks")).getArr?)
    let term := Json.mkObj [("variant",toJson variant), ("status",toJson ("supported" : String)),
      (required,toJson (0 : Nat)), (optional,toJson (0 : Nat)),
      ("unwind",Json.mkObj [("kind",toJson ("Continue" : String))])]
    let block := setField blocks[0]! "terminator" (Json.mkObj [("kind",term)])
    let body := setField bodies[0]! "basic_blocks" (toJson #[block])
    let input := setField root "bodies" (toJson #[body])
    let checked ← must (validate input)
    let some scope := checked.summary.bodies[0]? | throw (IO.userError "edge body scope was lost")
    let context := ReferenceContext.checked checked.summary.tables.shape scope.shape
    let resolve := checked.summary.resolver scope scope.index
    let value ← must (DecoderValues.decodeValueUsing context resolve term "$.edge" .terminator none DecoderValues.emptyDecodeMemo)
    match value with
    | .terminator _ _ fields =>
      let some (_, .blockRef reference) := fields.find? (fun entry => entry.1 == optional)
        | throw (IO.userError s!"{variant}.{optional} did not retain a bounded block reference")
      unless reference.val == 0 do throw (IO.userError "optional edge ID changed")
    | _ => throw (IO.userError "optional edge lost its terminator")
    let badTerm := setField term optional (toJson (1 : Nat))
    let badBlock := setField block "terminator" (Json.mkObj [("kind",badTerm)])
    let badBody := setField body "basic_blocks" (toJson #[badBlock])
    match validate (setField root "bodies" (toJson #[badBody])) with
    | .ok _ => throw (IO.userError s!"out-of-range {variant}.{optional} was accepted")
    | .error _ => pure ()

private def checkScopeIsolation : IO Unit := do
  let root := bodySource 1 0
  let rows ← must ((← must (root.getObjVal? "bodies")).getArr?)
  let first := rows[0]!
  let other := setField first "locals" (toJson #[
    Json.mkObj [("local",toJson (0 : Nat))], Json.mkObj [("local",toJson (1 : Nat))]])
  for bodies in [#[first,other], #[other,first]] do
    let input := setField root "bodies" (toJson bodies)
    match validate input with
    | .ok _ => throw (IO.userError "another body's locals admitted an out-of-range reference")
    | .error reason =>
      unless reason.contains "local 1 is out of range (locals=1)" do
        throw (IO.userError s!"unexpected cross-body diagnostic: {reason}")

private def checkReferenceFailure (text : String) : IO Unit := do
  let input ← must (Json.parse text)
  let badTypes := toJson #[Json.mkObj [("type_id",toJson (0 : Nat))]]
  let dangling := Json.mkObj [("type_id",toJson (1000000000 : Nat))]
  let invalid := setField (setField input "types" badTypes) "synthetic_reference" dangling
  match decodeRuntimeJson invalid.compress with
  | .ok _ => throw (IO.userError "malformed type payload was accepted")
  | .error reason =>
    unless reason.contains "dangling type reference" do
      throw (IO.userError s!"reference validator did not reject the dangling input: {reason}")

private def checkReader (path : String) : IO Unit := do
  let text ← IO.FS.readFile path
  checkReferenceFailure text
  let full ← must (decodeJson text)
  let runtime ← must (decodeRuntimeJson text)
  let some a := full.document.checkedReferences | throw (IO.userError "full reader lost reference evidence")
  let some b := runtime.document.checkedReferences | throw (IO.userError "runtime reader lost reference evidence")
  unless a.summary.global.size == b.summary.global.size &&
      a.summary.bodies.size == b.summary.bodies.size do
    throw (IO.userError "full/runtime reference inventories differ")
  IO.println s!"ReferenceValidationChecks: {path}: {b.summary.global.size} global references, {b.summary.bodies.size} body scopes"

def main (args : List String) : IO Unit := do
  checkBodyBounds
  checkScopeIsolation
  checkOptionalEdges
  let checked ← must (validate (source 1))
  let references := checked.summary.global.filterMap fun occurrence =>
    match occurrence.reference with
    | .type reference => some (reference.sourceId, reference.position.val)
    | _ => none
  unless references.contains (1,0) && references.contains (0,1) do
    throw (IO.userError "permuted IDs did not retain their source row positions")
  match validate (source 2) with
  | .ok _ => throw (IO.userError "dangling type reference was accepted")
  | .error reason =>
    unless reason == "$.value: dangling type reference 2" do
      throw (IO.userError s!"unexpected dangling-reference diagnostic: {reason}")
  for path in args do checkReader path
  IO.println "ReferenceValidationChecks: passed"

#print axioms Miri.Input.ReferenceValidation.TableRef.exists_in_source
#print axioms Miri.Input.ReferenceValidation.validateUsing
