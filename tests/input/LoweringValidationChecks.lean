import Miri.Input

open Lean Miri.Input

private def must (result : Except String α) : IO α :=
  match result with | .ok value => pure value | .error error => throw (IO.userError error)

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def sameProgram (left right : LoweredProgram) : Bool := Id.run do
  if !decide (left.roots = right.roots ∧ left.instances = right.instances ∧
      left.promoted = right.promoted ∧ left.bundle.spans = right.bundle.spans ∧
      left.bundle.definitions = right.bundle.definitions ∧
      left.bundle.typeConstants = right.bundle.typeConstants) then return false
  if left.bundle.bodies.size != right.bundle.bodies.size then return false
  for (a,b) in left.bundle.bodies.zip right.bundle.bodies do
    if !decide (a.body = b.body ∧ a.spans = b.spans ∧ a.definitions = b.definitions ∧
        a.typeConstants = b.typeConstants) then return false
    if a.obligations != b.obligations || a.input.sourcePath != b.input.sourcePath ||
        !DecoderValues.jsonWireEq a.input.payload b.input.payload then return false
  return true

private def compare (input : ImportDocumentCore) (label : String) : IO Unit := do
  let expected := lowerCoreProgram input
  let actual ← lowerCoreProgramForProcess {} 3 input
  match expected, actual with
  | .error a, .error b => check (a == b) s!"{label}: first lowering error changed"
  | .ok a, .ok b => check (sameProgram a b) s!"{label}: MIR, IDs, spans, source binding or obligations changed"
  | _, _ => throw (IO.userError s!"{label}: lowering result class changed")

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected one genuine JSON or binary export")
  let decoded ← must (← decodeRuntimeBytesForProcess (← IO.FS.readBinFile path)
    (({} : Options).setBool `miri.parallelInput true))
  let input := decoded.document
  compare input "genuine input"
  let foreignRaw := { input with
    raw := .null, allocationWorldValidation := none, allocationParseBinding := none, rawReflexivity := none }
  compare foreignRaw "foreign raw document"
  let some body := input.bodies[0]? | throw (IO.userError "fixture needs a root body")
  let changed := { body with sourcePath := body.sourcePath ++ ".foreign" }
  compare { input with bodies := input.bodies.set! 0 changed } "foreign source path"
  if let some localDecl := body.locals[0]? then
    let bad := { body with locals := body.locals.set! 0 { localDecl with typeId := input.types.size + 100 } }
    compare { input with bodies := input.bodies.set! 0 bad } "mutated typed local"
  let core := body.toBodyCore
  let foreign := { core with sourcePath := core.sourcePath ++ ".foreign" }
  let values := #[core,foreign]
  let ctx := LowerContext.ofDocument input
  let misplaced : BodySourceValidationTable ctx.sourceDocument ctx.compilerValueMemo values :=
    ⟨#[⟨⟨1,by simp [values]⟩, BodySourceValidation.prepare _ _ foreign⟩]⟩
  check ((misplaced.get ⟨0,by simp [values]⟩).isNone) "misplaced source certificate accepted"
  let absent : BodySourceValidationTable ctx.sourceDocument ctx.compilerValueMemo values := ⟨#[]⟩
  check ((absent.get ⟨0,by simp [values]⟩).isNone) "absent source certificate accepted"
  IO.println "source lowering guards: exact MIR/IDs/spans/obligations, first errors and foreign/misplaced input controls PASS"
