import Miri.Frontend.FoundationSourceMir
import Miri.Input.Model.SourceConst

/-! One-way parsing of captured initializer MIR. Runtime queries consume only
this typed syntax; no JSON or fabricated diagnostic frame survives parsing. -/
namespace Miri.Frontend.Foundation.SourceConstParser
open Lean

def body (document : Document) (source : Json) : Except String Input.SourceConst.Body := do
  let locals ← source.getObjValAs? (Array Nat) "locals"
  let blocks ← source.getObjValAs? (Array Json) "blocks"
  unless !locals.isEmpty && !blocks.isEmpty && locals.all (· < document.types.size) do
    throw "initializer source locals/blocks/type references invalid"
  let context : SourceMirParser.Context := {
    types := document.types.size
    definitions := document.definitions.size
    locals := locals.size
    blocks := blocks.size
    scopes := 0
    allocations := (← document.source.getObjValAs? (Array Json) "source_allocations").size }
  let required ← (← source.getObjValAs? (Array Json) "required_consts").mapM (SourceMirParser.constant context)
  let blocks ← blocks.mapM fun block => do
    let statements ← (← block.getObjValAs? (Array Json) "statements").mapM (SourceMirParser.statementKind context)
    let terminator ← SourceMirParser.terminator context (← block.getObjVal? "terminator") none
    return ({statements,terminator} : Input.SourceConst.Block)
  return ⟨locals,required,blocks⟩
end Miri.Frontend.Foundation.SourceConstParser
