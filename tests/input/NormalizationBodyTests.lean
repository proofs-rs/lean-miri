import Miri.Input.CompilerConstantQueries
import Miri.Input.Reader.PlaceTypes

open Lean Miri.Input Miri.MIR

private def must (value : Except String α) : IO α :=
  match value with
  | .ok result => pure result
  | .error message => throw (IO.userError message)

private def setField (value : Json) (key : String) (replacement : Json) : Json :=
  match value with
  | .obj fields => Json.mkObj ((key,replacement) :: fields.toList.filter (·.1 != key))
  | _ => value

private def arrayEqual (left right : Array α) (equal : α → α → Bool) : Bool :=
  left.size == right.size && (left.toList.zip right.toList).all fun (a,b) => equal a b

private def resultEqual : Except String Miri.Interpreter.CompilerConstantEvidence →
    Except String Miri.Interpreter.CompilerConstantEvidence → Bool
  | .error a,.error b => a == b
  | .ok a,.ok b => a.fnInstance == b.fnInstance && a.original == b.original &&
      a.normalized == b.normalized && a.span == b.span && a.value == b.value
  | _,_ => false

private def evidenceEqual (left right : CompilerConstantQueries.Prepared) : Bool :=
  arrayEqual left.bodies right.bodies fun left right =>
    match left,right with
    | .error a,.error b => a == b
    | .ok a,.ok b => arrayEqual (a.filterMap id) (b.filterMap id) resultEqual
    | _,_ => false

private def duplicateChecks : IO Unit := do
  let constant (value : ConstValue) (span : SpanRef := ⟨0⟩) : ConstantNode :=
    ⟨⟨span,none,.Val value 0⟩,.ok value⟩
  let source := constant .ZeroSized
  let normalized := constant (.Scalar (.Int 1 1))
  let info : Miri.MIR.SourceInfo := ⟨⟨0⟩,0⟩
  let body (block : Nat) : BodyNode := ⟨.Built,0,none,#[0],#[⟨block⟩],1,#[]⟩
  let tables : SyntaxTables := {
    constants := #[some source,some normalized,some normalized]
    projections := #[]
    projectionLists := #[some #[]]
    places := #[some ⟨0,0,⟨0⟩⟩]
    operands := #[some (.Constant ⟨0⟩),some (.Constant ⟨1⟩),some (.Constant ⟨2⟩)]
    rvalues := #[some (.BinaryOp .Add ⟨0⟩ ⟨0⟩),some (.BinaryOp .Add ⟨1⟩ ⟨2⟩)]
    statements := #[some ⟨info,.Assign ⟨0⟩ ⟨0⟩⟩,some ⟨info,.Assign ⟨0⟩ ⟨1⟩⟩]
    terminators := #[some ⟨info,.Return⟩]
    blocks := #[some ⟨#[⟨0⟩],⟨0⟩,false⟩,some ⟨#[⟨1⟩],⟨0⟩,false⟩]
    bodies := #[some (body 0),some (body 1)] }
  let mapping ← must (Reader.PlaceTypeReader.build tables ⟨0⟩ ⟨1⟩)
  unless mapping.constants == #[(⟨0⟩,⟨1⟩)] do
    throw (IO.userError "repeated source constant did not retain its first equivalent normalization")
  let conflicting := {tables with constants := tables.constants.set! 2 (some (constant (.Scalar (.Int 2 1))))}
  unless Reader.PlaceTypeReader.build conflicting ⟨0⟩ ⟨1⟩ ==
      .error "source constant has conflicting normalization in one body" do
    throw (IO.userError "conflicting normalization for a shared source constant was accepted")
  let wrongSpan := {tables with constants := tables.constants.set! 2 (some (constant (.Scalar (.Int 1 1)) ⟨1⟩))}
  unless Reader.PlaceTypeReader.build wrongSpan ⟨0⟩ ⟨1⟩ == .error "normalization changed constant span" do
    throw (IO.userError "normalization changed a shared constant span")

private def changed (root source context : Json) (bodies : Array Json) (index : Nat)
    (normalization : Json) : Json :=
  let source := setField source "constant_query_context" (setField context "normalization" normalization)
  setField root "bodies" (Json.arr (bodies.set! index source))

private def rejected (input : Json) (bodyIndex : Nat) : IO Unit := do
  match decodeRuntimeJson input.compress with
  | .error _ => pure ()
  | .ok decoded =>
    let tables := decoded.document.mirTables
    let some (.error _) := tables.normalizedBodies[bodyIndex]? |
      throw (IO.userError "malformed normalization retained a normalized body ID")
    let some (.error _) := tables.normalization[bodyIndex]? |
      throw (IO.userError "malformed normalization retained a usable constant/place mapping")

def main (args : List String) : IO Unit := do
  duplicateChecks
  let [path] := args | throw (IO.userError "expected shared-graph exporter JSON path")
  let text ← IO.FS.readFile path
  let root ← must (Json.parse text)
  let catalog ← must (Reader.Catalog.parse root)
  unless !catalog.nodes.isEmpty do throw (IO.userError "fixture does not exercise shared nodes")
  let bodies ← must (catalog.array (← must (catalog.field catalog.root "bodies" "$")) "bodies")
  let some raw := bodies[0]? | throw (IO.userError "fixture has no source body")
  let source ← must (catalog.inspect raw "body")
  let context ← must (catalog.inspect (← must (catalog.field source "constant_query_context" "body")) "context")
  let supported (fields : List (String × Json)) := Json.mkObj (("status",toJson "supported") :: fields)
  let compact := changed root source context bodies 0 (supported [("body_ref",toJson "source_body")])
  let embedded := changed root source context bodies 0 (supported [("body",source)])
  let compactDecoded ← must (decodeRuntimeJson compact.compress)
  let embeddedDecoded ← must (decodeRuntimeJson embedded.compress)
  let compactProgram ← must (lowerCoreProgram compactDecoded.document)
  let embeddedProgram ← must (lowerCoreProgram embeddedDecoded.document)
  unless compactProgram.roots == embeddedProgram.roots && compactProgram.instances == embeddedProgram.instances &&
      compactProgram.promoted == embeddedProgram.promoted &&
      compactProgram.bundle.bodies.map (·.body) == embeddedProgram.bundle.bodies.map (·.body) &&
      compactProgram.compilerTables == embeddedProgram.compilerTables &&
      compactProgram.input.obligations == embeddedProgram.input.obligations do
    throw (IO.userError "normalization encoding changed source MIR, compiler identities or obligations")
  let compactPrepared ← must (CompilerConstantQueries.prepare (← must (RuntimeProgram.ofProgram compactProgram)))
  let embeddedPrepared ← must (CompilerConstantQueries.prepare (← must (RuntimeProgram.ofProgram embeddedProgram)))
  unless evidenceEqual compactPrepared embeddedPrepared &&
      compactPrepared.obligations == embeddedPrepared.obligations do
    throw (IO.userError "source-body reference and identical embedded body changed constant evidence")
  let count : Nat := compactPrepared.bodies.foldl (fun n body => n +
    (body.toOption.map fun entries => (entries.filterMap fun entry => entry.bind Except.toOption).size).getD 0) 0
  unless count > 0 do throw (IO.userError "fixture contains no normalized constant query")
  for normalization in #[
      Json.mkObj [("status",toJson "unsupported"),("body",source)],
      supported [], supported [("body",source),("body_ref",toJson "source_body")],
      supported [("body_ref",toJson "other_body")],supported [("body_ref",toJson (42 : Nat))],
      supported [("body",toJson (42 : Nat))]] do
    rejected (changed root source context bodies 0 normalization) 0
  rejected (setField root "bodies" (Json.arr (bodies.set! 0 (toJson (42 : Nat))))) 0
  IO.println s!"typed normalization encodings, duplicate constants and fail-closed mappings: PASS ({count} constants)"
