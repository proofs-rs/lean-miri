import Miri.Input.Model

namespace Miri.Input.CheckedConstruction
open Lean DecoderValues ReferenceValidation

structure Source where
  summary : Summary
  bodies : Std.HashMap String BodyReferences

@[noinline] def Source.ofSummary (summary : Summary) : Source :=
  ⟨summary, summary.bodies.foldl (fun table scope => table.insert scope.path scope) {}⟩

private def localDecl (context : ReferenceContext) (resolve : ReferenceContext.Resolver context)
    (j : Json) (path : String) (memo : DecodeMemo) : Except String (LocalDecl context) := do
  let parsed ← parseLocal j path memo
  return ⟨parsed.id, ← resolve .type parsed.typeId, parsed.sourceInfo, parsed.payload⟩

private def node (context : ReferenceContext) (resolve : ReferenceContext.Resolver context)
    (wrapper : Json) (path : String) (domain : Domain) (memo : DecodeMemo) : Except String (MirNode context) := do
  let info ← parseSourceInfo (← field wrapper "source_info" path) (joinPath path "source_info") memo
  let value ← decodeValueUsing context resolve (← field wrapper "kind" path) (joinPath path "kind") domain none memo
  return ⟨value, info⟩

private def block (context : ReferenceContext) (resolve : ReferenceContext.Resolver context)
    (j : Json) (path : String) (memo : DecodeMemo) : Except String (BasicBlock context) := do
  let statements ← arrayField j "statements" path
  let statements ← statements.mapIdxM fun index value =>
    node context resolve value s!"{joinPath path "statements"}[{index}]" .statement memo
  let terminator ← field j "terminator" path
  if terminator == .null then throw s!"{path}: basic block has no terminator"
  return ⟨← fieldNat j "block" path, statements,
    ← node context resolve terminator (joinPath path "terminator") .terminator memo,
    ← fieldBool j "is_cleanup" path, j⟩

def bodyCore (source : Source) (_j : Json) (path fallback : String)
    (memo : DecodeMemo) : Except String BodyCore := do
  let some scope := source.bodies[path]?
    | throw s!"{path}: body is absent from the validated input"
  let context := ReferenceContext.checked source.summary.tables.shape scope.shape
  let index := scope.index
  let resolve := source.summary.resolver scope index
  let locals ← Vector.ofFnM fun index : Fin scope.localRows.size =>
    localDecl context resolve scope.localRows[index] s!"{joinPath path "locals"}[{index.val}]" memo
  let blocks ← Vector.ofFnM fun index : Fin scope.blockRows.size =>
    block context resolve scope.blockRows[index] s!"{joinPath path "basic_blocks"}[{index.val}]" memo
  parseBodyEnvelope context resolve scope.source path fallback locals.toArray blocks.toArray
    ⟨locals.size_toArray, blocks.size_toArray⟩ memo

def promoted (source : Source) (j : Json) (path fallback : String)
    (memo : DecodeMemo) : Except String (Array PromotedBody) :=
  parsePromotedBodies j path fallback memo (bodyCore source)

def body (source : Source) (j : Json) (path fallback : String)
    (memo : DecodeMemo) : Except String Body := do
  let core ← bodyCore source j path fallback memo
  return { toBodyCore := core, promotedBodies := ← promoted source j path fallback memo }

end Miri.Input.CheckedConstruction
