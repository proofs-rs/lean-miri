import Miri.Input.Reader.Terminators

namespace Miri.Input.Reader.BodyReader
open Lean Miri.MIR
abbrev Decode := MIRReader.Decode

private def phase (catalog : Catalog) (input : Json) (path : String) : Except String MirPhase := do
  let kind ← catalog.string (← catalog.field input "kind" path) path
  unless (← catalog.string (← catalog.field input "status" path) path) == "supported" do
    throw s!"{path}: unsupported MIR phase"
  if kind == "built" then return .Built
  let value ← catalog.string (← catalog.field input "phase" path) path
  match kind, value with
  | "analysis", "initial" => return .Analysis .Initial
  | "analysis", "post_cleanup" => return .Analysis .PostCleanup
  | "runtime", "initial" => return .Runtime .Initial
  | "runtime", "post_cleanup" => return .Runtime .PostCleanup
  | "runtime", "optimized" => return .Runtime .Optimized
  | _, _ => throw s!"{path}: unsupported MIR phase {kind}/{value}"

private def block (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode BlockNodeId := do
  return ⟨← catalog.readCached (·.tables.blocks) (fun state blocks => {state with tables := {state.tables with blocks}})
    (fun input path => do
      let statements ← (← catalog.array (← catalog.field input "statements" path) path).mapIdxM fun index input =>
        StatementReader.statement catalog ctx input s!"{path}.statements[{index}]"
      let terminator ← TerminatorReader.terminator catalog ctx (← catalog.field input "terminator" path) path
      return ⟨statements, terminator, ← catalog.boolean (← catalog.field input "is_cleanup" path) path⟩) input path⟩

def body (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode BodyId := do
  return ⟨← catalog.readCached (·.tables.bodies) (fun state bodies => {state with tables := {state.tables with bodies}})
    (fun input path => do
      let field := fun key => catalog.field input key path
      let phase ← phase catalog (← field "phase") path
      match ← catalog.optionalField input "injection_phase" path with
      | none | some .null => pure ()
      | some input => let _ ← BodyReader.phase catalog input path; pure ()
      let scopes ← catalog.array (← field "source_scopes") path
      let locals ← (← catalog.array (← field "locals") path).mapIdxM fun index input => do
        unless (← catalog.natural (← catalog.field input "local" path) path) == index do
          throw s!"{path}: noncontiguous local IDs"
        let info ← catalog.field input "source_info" path
        unless (← catalog.natural (← catalog.field info "scope" path) path) < scopes.size do
          throw s!"{path}: local source scope outside body"
        let id ← catalog.natural (← catalog.field (← catalog.field input "type" path) "type_id" path) path
        unless id < ctx.typeCount do throw s!"{path}: invalid local type ID {id}"
        return id
      let argumentCount ← catalog.natural (← field "arg_count") path
      unless argumentCount < locals.size do throw s!"{path}: argument count exceeds locals"
      let spread ← catalog.inspect (← field "spread_arg") path
      let spread ← if spread == .null then pure none else some <$> catalog.natural spread path
      if let some index := spread then
        unless index > 0 && index ≤ argumentCount do throw s!"{path}: invalid spread argument"
      let blocks ← (← catalog.array (← field "basic_blocks") path).mapIdxM fun index input => do
        unless (← catalog.natural (← catalog.field input "block" path) path) == index do
          throw s!"{path}: noncontiguous block IDs"
        block catalog ctx input s!"{path}.basic_blocks[{index}]"
      unless !blocks.isEmpty do throw s!"{path}: body has no entry block"
      let state ← get
      let mut annotated := Array.replicate locals.size false
      for id in blocks do
        let block ← state.tables.blocks.lookup id.index |>.mapError (fun id => s!"{path}: invalid block ID {id}")
        for id in block.statements do
          let statement ← state.tables.statements.lookup id.index |>.mapError (fun id => s!"{path}: invalid statement ID {id}")
          let annotation := match statement.kind with
            | .StorageLive id | .StorageDead id => some id
            | _ => none
          if let some id := annotation then
            if bound : id < annotated.size then annotated := annotated.set id true bound
            else throw s!"{path}: storage annotation outside locals"
      let alwaysLive := (Array.range locals.size).filter fun id =>
        id > argumentCount && annotated[id]? == some false
      return ⟨phase, argumentCount, spread, locals, blocks, scopes.size, alwaysLive⟩) input path⟩

end Miri.Input.Reader.BodyReader
