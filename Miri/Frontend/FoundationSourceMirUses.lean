import Miri.Frontend.Foundation
import Miri.Input.Model.SourceMirUses
namespace Miri.Frontend.Foundation.SourceMirUsesParser
open Lean Miri.Input SourceMirUses
private def place (j : Json) (argumentCount : Nat) : Except String Place := do
  let localId ← j.getObjValAs? Nat "local"
  unless localId ≤ argumentCount do throw "MIR use local is not a parameter/return place"
  let first ← j.getObjValAs? (Option String) "first_projection"
  let first ← first.mapM fun tag => match tag with
    | "deref" => pure ProjectionHead.deref | "other" => pure .other
    | _ => throw "MIR use projection head unsupported"
  return ⟨localId,first⟩
private def context (j : Json) : Except String Context := do
  match ← j.getObjValAs? String "kind" with
  | "non_use" => return .nonUse
  | "mutating" =>
    let value ← match ← j.getObjValAs? String "context" with
      | "Store" => pure MutatingContext.store | "SetDiscriminant" => pure .setDiscriminant
      | "AsmOutput" => pure .asmOutput | "Call" => pure .call | "Yield" => pure .yield
      | "Drop" => pure .drop | "Borrow" => pure .borrow | "RawBorrow" => pure .rawBorrow
      | "Projection" => pure .projection | _ => throw "MIR use mutating context unsupported"
    return .mutating value
  | "non_mutating" =>
    let value ← match ← j.getObjValAs? String "context" with
      | "Inspect" => pure NonMutatingContext.inspect | "Copy" => pure .copy | "Move" => pure .move
      | "SharedBorrow" => pure .sharedBorrow | "FakeBorrow" => pure .fakeBorrow
      | "RawBorrow" => pure .rawBorrow | "PlaceMention" => pure .placeMention
      | "Projection" => pure .projection | _ => throw "MIR use nonmutating context unsupported"
    return .nonMutating value
  | _ => throw "MIR use context kind unsupported"
def material (d : Document) : Except String (Option SourceMirUses.Material) := do
  let source ← match d.source.getObjVal? "mir_use_source" with
    | .error _ | .ok .null => return none | .ok value => pure value
  let mut rows : Array SourceMirUses.Declaration := #[]
  for row in (← source.getObjValAs? (Array Json) "declarations") do
    let id ← row.getObjValAs? Nat "definition"
    let some definition := d.definitions[id]? | throw "MIR use owner definition absent"
    unless (← definition.getObjValAs? Nat "definition_id") == id do throw "MIR use definition identity mismatch"
    let raw : DefinitionId := ⟨← definition.getObjValAs? Nat "crate_index",← definition.getObjValAs? Nat "index"⟩
    unless !(rows.any (·.definition == raw)) do throw "MIR use definition duplicated"
    let source ← row.getObjVal? "body"
    let body ← if source == .null then pure none else do
      unless (← source.getObjValAs? Nat "source_definition") == id do throw "MIR use source owner mismatch"
      let blocks ← source.getObjValAs? (Array Nat) "block_statement_counts"
      let count ← source.getObjValAs? Nat "argument_count"
      let spread ← source.getObjValAs? (Option Nat) "spread_argument"
      if let some index := spread then unless index > 0 && index ≤ count do throw "MIR use spread argument invalid"
      let phase ← source.getObjVal? "phase"
      unless (← phase.getObjValAs? String "kind") == "runtime" && (← phase.getObjValAs? String "phase") == "optimized" do
        throw "MIR use body is not optimized runtime source"
      let rawEvents ← source.getObjValAs? (Array Json) "events"
      unless rawEvents.size == (← source.getObjValAs? Nat "event_count") do throw "MIR use event count mismatch"
      let events ← rawEvents.mapM fun event => do
        let value ← event.getObjVal? "kind"
        let kind : SourceMirUses.Kind ← match ← value.getObjValAs? String "kind" with
          | "place" => pure (SourceMirUses.Kind.place (← place (← value.getObjVal? "place") count) (← context (← value.getObjVal? "context")))
          | "call_move" => pure (SourceMirUses.Kind.callMove (← place (← value.getObjVal? "place") count))
          | "tail_call" => pure Kind.tailCall
          | _ => throw "MIR use event kind unsupported"
        let block ← event.getObjValAs? Nat "block"
        let statement ← event.getObjValAs? Nat "statement"
        let some length := blocks[block]? | throw "MIR use block absent"
        unless statement ≤ length do throw "MIR use location outside source block"
        return Event.mk block statement kind
      pure (some (Body.mk count spread (.known (.Runtime .Optimized)) blocks events))
    let source ← row.getObjVal? "compilation"
    let compilation ← if source == .null then pure none else do
      let optimization ← match ← source.getObjValAs? String "optimization" with
        | "No" => pure Optimization.no | "Less" => pure .less | "More" => pure .more
        | "Aggressive" => pure .aggressive | "Size" => pure .size | "SizeMin" => pure .sizeMin
        | _ => throw "MIR defining optimization option unsupported"
      let freeze ← match source.getObjVal? "freeze_lang_item_present" with
        | .error _ => pure none | .ok value => fromJson? value
      pure (some (Compilation.mk optimization (← source.getObjValAs? Bool "incremental") freeze))
    let alwaysConst ← match row.getObjVal? "always_const" with
      | .error _ => pure none | .ok value => fromJson? value
    for previous in rows do
      if previous.definition.crateIndex == raw.crateIndex then
        unless previous.compilation == compilation do
          throw "defining crate compilation source contradicts"
    rows := rows.push ⟨raw,body,compilation,alwaysConst⟩
  return some ⟨rows⟩
end Miri.Frontend.Foundation.SourceMirUsesParser
