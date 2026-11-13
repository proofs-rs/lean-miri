import Miri.Input.MirTemplateCodec

/-! Complete transformed coroutine MIR comparisons against the pinned compiler's
independent instance normalization. Type and definition IDs are comparison-local
identities; this test does not establish executable World/provider integration. -/
open Lean Miri.Input Miri.Input.GenericSubstitution
private def must (value : Except String α) : IO α :=
  match value with | .ok value => pure value | .error error => throw (IO.userError error)
private def terms : Terms → Array GenericSubstitution.Term
  | .nil => #[] | .cons head tail => #[head] ++ terms tail
private def check (row : Json) : Except String Unit := do
  let source ← MirTemplateCodec.readTemplate (← row.getObjVal? "source")
  let expected ← MirTemplateCodec.readTemplate (← row.getObjVal? "expected")
  let arguments ← (← (← row.getObjVal? "arguments").getArr?).mapM (GenericMaterialCodec.readTerm 16384)
  let resolve (term : GenericSubstitution.Term) : Except String Nat := do
    let term ← MirTemplate.eraseFreeRegions 16384 term
    let some id := expected.types.findIdx? (· == term) | throw "source MIR type differs from compiler oracle"
    pure id
  let aggregate (id variant : Nat) : Except String Miri.MIR.AggregateKind := do
    let some term := expected.types[id]? | throw "aggregate type absent"
    let .definition .type "adt" owner children := term | throw "aggregate source type is not ADT"
    let arguments ← (terms children).mapM fun term => do
      match term.sort with
      | .type => return Miri.MIR.GenericArg.Type (← resolve term)
      | .region => pure (.Lifetime .Erased)
      | _ => throw "comparison aggregate argument outside type/region domain"
    pure (.Adt (owner.crateIndex*2^32+owner.index) variant arguments none none)
  let actual ← MirTemplate.instantiate source 16384 arguments resolve aggregate
  let reference ← MirTemplate.instantiate expected 16384 arguments resolve aggregate
  unless actual == reference do throw "complete transformed coroutine MIR differs from pinned normalized body"
  unless source.parameters.isEmpty || (MirTemplate.instantiate source 16384 arguments.pop resolve aggregate).toOption.isNone do
    throw "missing coroutine MIR arguments accepted"
  let broken := {source with skeleton := {source.skeleton with locals := source.skeleton.locals.push ⟨source.types.size⟩}}
  unless (MirTemplate.instantiate broken 16384 arguments resolve aggregate).toOption.isNone do
    throw "missing coroutine MIR type slot accepted"
  let some block := source.skeleton.blocks[0]? | throw "oracle source has no blocks"
  let addStatement (kind : MirTemplate.StatementKind) := {source with skeleton := {source.skeleton with
    blocks := source.skeleton.blocks.set! 0 {block with statements := block.statements.push ⟨block.terminator.source,kind⟩}}}
  let invalidProjection := addStatement (.sourceAssign ⟨0,#[.field 0 ⟨source.types.size⟩]⟩
    (.discriminant ⟨0,#[]⟩))
  unless (MirTemplate.validateStructure invalidProjection).toOption.isNone do
    throw "missing projected field type slot accepted"
  let invalidScalar := addStatement (.sourceAssign ⟨0,#[]⟩
    (.use (.scalar ⟨0⟩ ⟨0⟩ (2^128) 16) .No))
  unless (MirTemplate.validateStructure invalidScalar).toOption.isNone do
    throw "overflowing source scalar accepted"
  let invalidAssertion := {source with skeleton := {source.skeleton with
    blocks := source.skeleton.blocks.set! 0 {block with terminator := {block.terminator with
      kind := .assertResume (.zeroSized ⟨0⟩ ⟨0⟩) false .NullPointerDereference 0 .Unreachable}}}}
  unless (MirTemplate.validateStructure invalidAssertion).toOption.isNone do
    throw "non-coroutine assertion admitted by resume source category"
  let invalidIndex := addStatement (.sourceAssign ⟨0,#[.index source.skeleton.locals.size]⟩
    (.discriminant ⟨0,#[]⟩))
  unless (MirTemplate.validateStructure invalidIndex).toOption.isNone do
    throw "missing projected index local accepted"
  let invalidCast := addStatement (.sourceAssign ⟨0,#[]⟩
    (.cast .IntToInt (.zeroSized ⟨0⟩ ⟨0⟩) ⟨source.types.size⟩))
  unless (MirTemplate.validateStructure invalidCast).toOption.isNone do
    throw "missing source cast type slot accepted"
  let invalidCleanup := {source with skeleton := {source.skeleton with
    blocks := source.skeleton.blocks.set! 0 {block with terminator := {block.terminator with
      kind := .sourceCall ⟨0⟩ ⟨0⟩ #[] ⟨0,#[]⟩ none (.Cleanup source.skeleton.blocks.size) ⟨0⟩}}}}
  unless (MirTemplate.validateStructure invalidCleanup).toOption.isNone do
    throw "invalid source call cleanup target accepted"
  match MirTemplate.instantiate source 16384 arguments (fun _ => .error "source type unavailable") aggregate with
  | .error "source type unavailable" => pure ()
  | _ => throw "coroutine MIR source type error did not propagate"

def main (args : List String) : IO Unit := do
  let [path] := args | throw (IO.userError "expected fresh coroutine MIR oracle JSON")
  let rows ← must ((← must (Json.parse (← IO.FS.readFile path))).getArr?)
  unless rows.size == 38 do throw (IO.userError "expected 38 complete extended source body comparisons")
  for row in rows do must (check row)
  IO.println "PASS 38 complete extended source MIR comparisons and typed malformed/source-error controls"
