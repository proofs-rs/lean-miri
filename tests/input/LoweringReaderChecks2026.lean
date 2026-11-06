import Miri.Input.LowerMIR

/-! Finite reference comparison for the removed re-decode guard. The reference
is retained only here; production lowering consumes reader-constructed MIR. -/
open Lean Miri.Input

private def legacyTypedValueMatchesSource (source : Lean.Json) (path : String)
    (value : TypedValue) : Bool := Id.run do
  let some raw := jsonAtPath source path | return false
  match decodeCompilerValue raw with
  | .ok decoded => return decoded == value
  | .error _ => return false

/-- Recheck that the typed MIR nodes used by lowering are exactly the ones
decoded from the same raw body. Retaining only a raw payload/path is not enough:
callers can construct or mutate an ImportDocument after decoding. -/
private def legacySourceBodyMatches (source : Lean.Json) (input : BodyCore) : Bool := Id.run do
  unless input.sourcePath.startsWith "$." && jsonAtPath source input.sourcePath == some input.payload do
    return false
  let some rawBlocks := ((input.payload.getObjVal? "basic_blocks").bind Lean.Json.getArr?).toOption
    | return false
  unless rawBlocks.size == input.blocks.size do return false
  for (block, index) in input.blocks.toList.zipIdx do
    let some rawBlock := rawBlocks[index]? | return false
    unless block.payload == rawBlock do return false
    unless (rawBlock.getObjValAs? Nat "block").toOption == some block.id do return false
    let some rawStatements := ((rawBlock.getObjVal? "statements").bind Lean.Json.getArr?).toOption
      | return false
    unless rawStatements.size == block.statements.size do return false
    for (node, statementIndex) in block.statements.toList.zipIdx do
      let path := s!"{input.sourcePath}.basic_blocks[{index}].statements[{statementIndex}].kind"
      unless legacyTypedValueMatchesSource source path node.value do return false
    let terminatorPath := s!"{input.sourcePath}.basic_blocks[{index}].terminator.kind"
    unless legacyTypedValueMatchesSource source terminatorPath block.terminator.value do return false
  return true


private def must (value : Except String α) : IO α :=
  match value with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

private def check (document : ImportDocumentCore) : IO Nat := do
  let program ← must (lowerCoreProgram document)
  let context := LowerContext.ofDocument document
  for lowered in program.bundle.bodies do
    unless legacySourceBodyMatches document.raw lowered.input do
      throw (IO.userError s!"reader body would fail the removed guard: {lowered.input.sourcePath}")
    let actual ← must (lowerBody context lowered.input)
    let source := if legacySourceBodyMatches document.raw lowered.input then some document.raw else none
    let reference ← must (lowerBody { context with sourceDocument := source } lowered.input)
    unless actual.body == reference.body && actual.spans == reference.spans &&
        actual.definitions == reference.definitions && actual.typeConstants == reference.typeConstants &&
        actual.obligations == reference.obligations do
      throw (IO.userError s!"reader lowering differs from reference: {lowered.input.sourcePath}")
  return program.bundle.bodies.size

def main (args : List String) : IO Unit := do
  let path := args.headD "examples/empty_function/input.json"
  let text ← IO.FS.readFile path
  let full ← must (decodeJson text)
  let runtime ← must (decodeRuntimeJson text)
  let a ← check full.document.toCore
  let b ← check runtime.document
  unless a == b do throw (IO.userError "full/runtime body counts differ")
  IO.println s!"LoweringReaderChecks: {a} full + {b} runtime root/instance/promoted bodies match removed-guard reference"
