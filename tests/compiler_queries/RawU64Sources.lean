import Miri.Input.RawU64FrameCodec
open Lean Miri.Input
private def must (value : Except String A) : IO A :=
  match value with | .ok result => pure result | .error error => throw (IO.userError error)
private def check (value : Bool) (message : String) : IO Unit :=
  unless value do throw (IO.userError message)
def main (args : List String) : IO Unit := do
  let [casesPath,rowsPath] := args | throw (IO.userError "expected raw codec cases and actual Rust source rows")
  let cases ← must ((← must (Json.parse (← IO.FS.readFile casesPath))).getArr?)
  let mut positive := 0
  let mut negative := 0
  for row in cases do
    let name ← must ((← must (row.getObjVal? "name")).getStr?)
    let expected ← must ((← must (row.getObjVal? "accepted")).getBool?)
    let actual := RawU64FrameCodec.read (← must (row.getObjVal? "source"))
    check (actual.isOk == expected) s!"codec expectation failed for {name}: {reprStr actual}"
    if expected then positive := positive + 1 else negative := negative + 1
  let rows ← must ((← must (Json.parse (← IO.FS.readFile rowsPath))).getArr?)
  let sources ← rows.mapM (fun row => must (RawU64FrameCodec.read row))
  check (sources.size == 3 && positive == 3 && negative == 17) "raw source control counts differ"
  for (source,index) in sources.zipIdx do
    check (source.definition == (⟨2,#[69102,54220,38452][index]!⟩ : GenericSubstitution.DefinitionIdentity)) "physical source owner differs"
    let .rawU64 program := source.program | throw (IO.userError "policy did not retain typed raw program")
    check (program.localCount == 1 && source.localSources.size == 1 && source.statementSources.size == 1 && source.terminatorSources.size == 1)
      "raw source metadata lost physical local/block domains"
    check (!program.defPath.isEmpty) "physical source def_path absent"
    if index == 0 then
      check (program.ownerKind == .anonymousConstant && program.required.size == 1 && program.required[0]?.any (·.definition == ⟨2,54180⟩))
        "anonymous source preamble/owner kind lost"
    if index == 1 then
      check (program.ownerKind == .associatedConstant && program.required.size == 1 && program.required[0]?.any (·.definition == ⟨2,38452⟩))
        "associated source preamble/owner kind lost"
    if index == 2 then
      check (program.ownerKind == .associatedConstant && program.required.isEmpty) "leaf source header/preamble changed"
      let #[.assign 0 (.unaryNot (.sourceValue value))] := program.statements
        | throw (IO.userError "actual leaf is not raw UnaryNot source")
      check (value.kind == .literalValue && value.value == 0 && value.userType.isNone) "raw u64 literal source class/value changed"
    check (!(CtfeMirSource.stackSource source).isOk) "raw external source relabeled into local legacy stack"
  IO.println s!"raw u64 source controls PASS: {positive} actual external frames, {negative} strict negative cases; typed headers/preambles/UnaryNot preserved; no compiler-root result claimed"
