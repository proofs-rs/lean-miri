import Miri.Input.Reader.Rvalues

namespace Miri.Input.Reader.StatementReader
open Lean Miri.MIR

abbrev State := MIRReader.State
abbrev Decode := MIRReader.Decode

def sourceInfo (catalog : Catalog) (input : Json) (path : String) : Decode MIR.SourceInfo := do
  return ⟨← ConstantReader.span catalog (← catalog.field input "span" path) path,
    ← catalog.natural (← catalog.field input "scope" path) path⟩

private def definition (catalog : Catalog) (input : Json) (path : String) : Decode DefId :=
  GenericReader.definition catalog input path

private def fakeRead (catalog : Catalog) (input : Json) (path : String) : Decode FakeReadCause := do
  let hoisted := do
    let value ← catalog.inspect (← catalog.field input "hoisted_from" path) path
    if value == .null then pure none else some <$> definition catalog value path
  match ← catalog.string (← catalog.field input "kind" path) path with
  | "match_guard" => return .ForMatchGuard
  | "matched_place" => return .ForMatchedPlace (← hoisted)
  | "guard_binding" => return .ForGuardBinding
  | "let_binding" => return .ForLet (← hoisted)
  | "index" => return .ForIndex
  | kind => throw s!"{path}: unsupported fake read {kind}"

private def coverage (catalog : Catalog) (input : Json) (path : String) : Decode CoverageKind := do
  let field := fun key => catalog.field input key path
  match ← catalog.string (← field "kind") path with
  | "point" =>
    let kind ← match ← catalog.string (← field "point_kind") path with
      | "expr" => pure CoveragePointKind.Expr
      | "implicit_else" => pure .ImplicitElse
      | "function_end" => pure .FunctionEnd
      | kind => throw s!"{path}: unsupported coverage point {kind}"
    let hir ← field "hir_id"
    return .Point kind ⟨← definition catalog (← catalog.field hir "owner_def_id" path) path,
      ← catalog.natural (← catalog.field hir "local_id" path) path⟩
  | "block_marker" => return .BlockMarker (← catalog.natural (← field "id") path)
  | "virtual_counter" => return .VirtualCounter (← catalog.natural (← field "bcb") path)
  | kind => throw s!"{path}: unsupported coverage kind {kind}"

private def userProjection (catalog : Catalog) (input : Json) (path : String) : Except String MIR.UserTypeProjection := do
  let projections : Array MIR.ProjectionKind ← (← catalog.array (← catalog.field input "projections" path) path).mapM fun input => do
    let field := fun key => catalog.field input key path
    let natural := fun key => do catalog.natural (← field key) path
    let boolean := fun key => do catalog.boolean (← field key) path
    match ← catalog.string (← field "kind") path with
    | "Deref" => return .Deref
    | "Field" => return .Field (← natural "index")
    | "Index" => return .Index
    | "ConstantIndex" => return .ConstantIndex (← natural "offset") (← natural "min_length") (← boolean "from_end")
    | "Subslice" => return .Subslice (← natural "from") (← natural "to") (← boolean "from_end")
    | "Downcast" =>
      let name ← catalog.inspect (← field "name") path
      let name ← if name == .null then pure none else some <$> catalog.string name path
      return .Downcast name (← natural "variant_index")
    | "OpaqueCast" => return .OpaqueCast
    | "UnwrapUnsafeBinder" => return .UnwrapUnsafeBinder
    | "PhantomDeref" => return .PhantomDeref
    | kind => throw s!"{path}: unsupported user projection {kind}"
  return ⟨← catalog.natural (← catalog.field input "base_index" path) path, projections⟩

private def kind (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode StatementKindNode := do
  let field := fun key => catalog.field input key path
  let natural := fun key => do catalog.natural (← field key) path
  let place := do OperandReader.place catalog ctx.typeCount (← field "place") path
  let operand := fun key => do OperandReader.operand catalog ctx (← field key) path
  unless (← catalog.string (← field "status") path) == "supported" do throw s!"{path}: unsupported statement"
  match ← catalog.string (← field "variant") path with
  | "Assign" => return .Assign (← place) (← RvalueReader.rvalue catalog ctx (← field "rvalue") path)
  | "StorageLive" => return .StorageLive (← natural "local")
  | "StorageDead" => return .StorageDead (← natural "local")
  | "PlaceMention" => return .PlaceMention (← place)
  | "SetDiscriminant" => return .SetDiscriminant (← place) (← natural "variant_index")
  | "ConstEvalCounter" => return .ConstEvalCounter
  | "Nop" => return .Nop
  | "FakeRead" => return .FakeRead (← fakeRead catalog (← field "cause") path) (← place)
  | "AscribeUserType" =>
    let variance ← match ← catalog.string (← catalog.field (← field "variance") "kind" path) path with
      | "covariant" => pure Variance.Covariant
      | "contravariant" => pure .Contravariant
      | "invariant" => pure .Invariant
      | "bivariant" => pure .Bivariant
      | kind => throw s!"{path}: unsupported variance {kind}"
    return .AscribeUserType (← place) (← userProjection catalog (← field "user_type_projection") path) variance
  | "Coverage" => return .Coverage (← coverage catalog (← field "coverage") path)
  | "Intrinsic" =>
    match ← catalog.string (← field "intrinsic") path with
    | "Assume" => return .Intrinsic (.Assume (← operand "value"))
    | "CopyNonOverlapping" => return .Intrinsic (.CopyNonOverlapping ⟨← operand "src", ← operand "dst", ← operand "count"⟩)
    | kind => throw s!"{path}: unsupported intrinsic {kind}"
  | "BackwardIncompatibleDropHint" =>
    unless (← catalog.string (← catalog.field (← field "reason") "kind" path) path) == "edition_2024" do
      throw s!"{path}: unsupported backward drop reason"
    return .BackwardIncompatibleDropHint (← place) .Edition2024
  | kind => throw s!"{path}: unsupported statement variant {kind}"

def statement (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode StatementId := do
  return ⟨← catalog.readCached (·.tables.statements) (fun state statements => {state with tables := {state.tables with statements}})
    (fun input path => do
      let kind ← kind catalog ctx (← catalog.field input "kind" path) path
      return ⟨← sourceInfo catalog (← catalog.field input "source_info" path) path, kind⟩) input path⟩


end Miri.Input.Reader.StatementReader
