import Miri.Input.CallResolution
import empty_function.Meaning
import Lean.Elab.Deriving.ToExpr

/-! Fixed Rust input and the actual production-lowered empty function.
Reflection constructs ordinary safe constants. It is part of the explicitly
trusted compiler/import boundary and supplies no execution-success premise. -/

set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

namespace EmptyFunction.Program
open Lean Miri Miri.Input Miri.Interpreter Miri.MIR

deriving instance ToExpr for Except

open Lean Elab Command in
private partial def deriveQuote (name : Name) : StateT NameSet CommandElabM Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  let some info := (← getEnv).find? name | return
  if !name.toString.startsWith "Miri." then return
  match info with
  | .inductInfo indInfo =>
    let existing ← liftM <| liftTermElabM <| Meta.forallTelescopeReducing indInfo.type fun xs _ => do
      Meta.synthInstance? (← Meta.mkAppM ``ToExpr
        #[mkAppN (mkConst name (indInfo.levelParams.map Level.param)) xs])
    if existing.isSome then return
    for ctor in indInfo.ctors do
      for dependency in (← getConstInfo ctor).type.getUsedConstants do
        if dependency != name then deriveQuote dependency
    liftM <| elabCommand (← `(deriving instance ToExpr for $(mkIdent name)))
  | .defnInfo definition =>
    let typeFormer ← liftM <| liftTermElabM <|
      Meta.forallTelescopeReducing definition.type fun _ body => pure body.isSort
    if typeFormer then
      for dependency in definition.value.getUsedConstants do
        if dependency != name then deriveQuote dependency
  | _ => pure ()

open Lean Elab Command in
run_cmd do
  discard <| (deriveQuote ``LoadedBody).run {}
  discard <| (deriveQuote ``CallInstance).run {}

structure Root where
  functionInstance : CallInstance
  loaded : LoadedBody
  deriving ToExpr

private def reflectRoot : IO (Except String Root) := do
  let decoded ← Input.decodeFile "examples/empty_function/input.json"
  return do
    let decoded ← decoded
    let lowered ← Input.lowerProgram decoded.document
    let prepared ← CallResolution.prepare lowered
    let definition ← prepared.program.rootDefinitionId 0
    let functionInstance : CallInstance := ⟨.Item definition, #[]⟩
    pure ⟨functionInstance, ← CallResolution.loadedBodyOfInstance prepared functionInstance⟩

open Lean Elab Command in
run_cmd do
  let result ← liftIO reflectRoot
  let value ← match result with
    | .ok value => pure value
    | .error reason => throwError "empty_function production lowering failed: {reason}"
  liftCoreM <| addDecl <| .defnDecl {
    name := `EmptyFunction.Program.root, levelParams := [], type := mkConst ``Root
    value := toExpr value, hints := .regular 0, safety := .safe }

/-- A checked source-shaped observation, used only by proof statements. The
interpreter continues to retain and evaluate the original syntax IDs. -/
noncomputable def contents : Miri.MIR.Body :=
  (Miri.MIR.Contents.body root.loaded.tables #[] root.loaded.body).toOption.get (by with_unfolding_all decide)

theorem contents_checked :
    Miri.MIR.Contents.body root.loaded.tables #[] root.loaded.body = .ok contents := by with_unfolding_all rfl

theorem contents_unit_assignment :
    ∃ literal, ((contents.basicBlocks[0]?).bind (fun block => block.statements[0]?)).map
      (fun statement => statement.kind) =
        some (.Assign ⟨0,#[]⟩ (.Use (.Constant literal) .Yes)) := by
  with_unfolding_all exact ⟨_, rfl⟩

theorem contents_cleanup : (contents.basicBlocks[0]?).map (·.cleanup) = some false := by
  with_unfolding_all rfl

theorem contents_statement_count : (contents.basicBlocks[0]?).map (fun block => block.statements.size) = some 1 := by
  with_unfolding_all rfl

theorem contents_return : (contents.basicBlocks[0]?).map (fun block => block.terminator.kind) = some .Return := by
  with_unfolding_all rfl

theorem no_arguments : root.loaded.body.argumentCount = 0 := by rfl
theorem one_local : root.loaded.body.locals.size = 1 := by rfl
theorem one_block : root.loaded.body.basicBlocks.size = 1 := by rfl
noncomputable def blockId : Miri.MIR.BlockNodeId := root.loaded.body.basicBlocks[0]'(by decide)
noncomputable def block : Miri.MIR.BlockNode :=
  (root.loaded.tables.blocks.lookup blockId.index).toOption.get (by decide)
noncomputable def terminator : Miri.MIR.TerminatorNode :=
  (root.loaded.tables.terminators.lookup block.terminator.index).toOption.get (by decide)

theorem one_statement : block.statements.size = 1 := by rfl
theorem normal_return : terminator.kind = .Return := by rfl
theorem no_cleanup : block.cleanup = false := by rfl

end EmptyFunction.Program

open Lean Elab Command in
run_cmd do
  for name in #[``EmptyFunction.Program.root, ``EmptyFunction.Program.contents,
      ``EmptyFunction.Program.contents_checked, ``EmptyFunction.Program.contents_unit_assignment,
      ``EmptyFunction.Program.contents_cleanup, ``EmptyFunction.Program.contents_statement_count,
      ``EmptyFunction.Program.contents_return,
      ``EmptyFunction.Program.no_arguments, ``EmptyFunction.Program.one_local, ``EmptyFunction.Program.one_block,
      ``EmptyFunction.Program.one_statement, ``EmptyFunction.Program.normal_return, ``EmptyFunction.Program.no_cleanup] do
    for dependency in (← collectAxioms name) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "unapproved empty_function reflection axiom: {dependency}"
