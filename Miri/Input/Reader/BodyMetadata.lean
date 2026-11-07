import Miri.Input.Reader.Instances
import Miri.Input.Reader.Constants

namespace Miri.Input.Reader.BodyMetadataReader
open Lean Miri.MIR
abbrev Decode := MIRReader.Decode

private def scope (catalog : Catalog) (typeCount count index : Nat) (input : Json) (path : String) : Decode SourceScopeData := do
  let field := fun key => catalog.field input key path
  unless (← catalog.natural (← field "scope") path) == index do throw s!"{path}: source scope ID differs from position"
  let parent := fun key => do
    let value ← catalog.inspect (← field key) path
    if value == .null then return none
    let parent ← catalog.natural value path
    unless parent < count && parent < index do throw s!"{path}: source scope parent is not an earlier scope"
    return some parent
  let _ ← parent "parent"
  let inlinedParent ← parent "inlined_parent_scope"
  let inlined ← catalog.inspect (← field "inlined") path
  if inlined == .null then return ⟨none,inlinedParent,none⟩
  let callee ← InstanceReader.read catalog typeCount inlined path
  let span ← ConstantReader.span catalog (← catalog.field inlined "callsite_span" path) path
  let track ← catalog.boolean (← catalog.field inlined "requires_caller_location" path) path
  return ⟨some (callee,span),inlinedParent,some track⟩

private def requiredConstants (catalog : Catalog) (ctx : ConstantReader.Context)
    (input : Json) (path : String) : Decode (Array (Except RequiredConstantFailure RequiredConstantCheck)) := do
  let original ← catalog.array (← catalog.field input "required_consts" path) path
  let context ← catalog.field input "constant_query_context" path
  let query ← catalog.field context "required_constant_checks" path
  catalog.requireSupported query path
  unless (← catalog.string (← catalog.field query "typing_env" path) path) == "body_typing_env" do
    throw "required-constant typing environment mismatch"
  let checks ← catalog.array (← catalog.field query "checks" path) path
  unless checks.size == original.size do throw "required-constant query count mismatch"
  checks.mapIdxM fun index check => do
    let some source := original[index]? | throw "required source operand absent"
    unless (← catalog.natural (← catalog.field check "index" path) path) == index do
      throw "required-constant source order mismatch"
    let sourceSpan ← ConstantReader.span catalog (← catalog.field source "span" path) path
    let checkSpan ← ConstantReader.span catalog (← catalog.field check "span" path) path
    unless sourceSpan == checkSpan do throw "required-constant source span mismatch"
    let result ← catalog.field check "result" path
    let status ← catalog.optionalField result "status" path
    if (status.bind fun value => (catalog.string value path).toOption) == some "supported" then
      let normalized ← catalog.field result "normalized_operand" path
      let normalizedSpan ← ConstantReader.span catalog (← catalog.field normalized "span" path) path
      unless normalizedSpan == sourceSpan do throw "required constant normalization changed source span"
      let source ← ConstantReader.constant catalog ctx source path
      let normal ← ConstantReader.constant catalog ctx normalized path
      let ty ← catalog.natural (← catalog.field (← catalog.field normalized "type" path) "type_id" path) path
      let value ← ConstantReader.evaluated catalog ctx ty (← catalog.field result "value" path) path
      return .ok ⟨⟨source⟩,⟨normal⟩,value⟩
    let kind ← catalog.optionalField result "kind" path
    let kind := kind.bind fun value => (catalog.string value path).toOption
    let reason := (← catalog.inspect result path).compress
    if kind == some "required_const_normalization_error" || kind == some "required_const_evaluation_error" then
      return .error (.invalidProgram s!"required constant compiler failure: {reason}")
    return .error (.unsupported s!"required constant unresolved: {reason}")

private def callSites (catalog : Catalog) (input : Json) (path : String) :
    Except String (Array (Except String (Option CallSiteData))) := do
  let blocks ← catalog.array (← catalog.field input "basic_blocks" path) path
  return blocks.mapIdx fun index block => do
    let path := s!"{path}.basic_blocks[{index}].terminator.kind"
    let kind ← catalog.field (← catalog.field block "terminator" path) "kind" path
    let variant ← catalog.string (← catalog.field kind "variant" path) path
    unless variant == "Call" || variant == "TailCall" do return none
    let source ← catalog.field kind "resolution" path
    let string := fun key => do catalog.string (← catalog.field source key path) path
    let natural := fun key => do catalog.natural (← catalog.field source key path) path
    return some {
      status := string "status"
      kind := string "kind"
      instanceId := natural "instance_id"
      dispatchSlot := natural "dispatch_slot"
      functionType := do
        let ty ← catalog.field source "function_type" path
        catalog.natural (← catalog.field ty "type_id" path) path }

def backtraceSpans (catalog : Catalog) (input : Json) (path : String) : Decode (Array BacktraceSpanData) := do
  let records ← catalog.array (← catalog.field input "backtrace_spans" path) path
  let mut entries := #[]
  for record in records do
    let span ← ConstantReader.span catalog (← catalog.field record "span" path) path
    let source ← catalog.field record "source_position" path
    let natural := fun key => do catalog.natural (← catalog.field source key path) path
    let offset ← natural "byte_position"
    unless offset < 2^32 do throw "compiler BytePos exceeds u32"
    let position : BacktracePositionData := ⟨UInt32.ofNat offset,← natural "line",
      ← natural "zero_based_char_column",← catalog.string (← catalog.field source "filename" path) path⟩
    unless (← catalog.natural (← catalog.field record "collapsed_lo" path) path) == position.bytePosition.toNat do
      throw "collapsed hygiene BytePos/source-map position mismatch"
    if let some previous := entries.find? (fun entry : BacktraceSpanData => entry.span == span) then
      unless previous.position == position do throw "conflicting body/span hygiene query"
    else entries := entries.push ⟨span,position⟩
  return entries

def read (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode BodySourceData := do
  let typeCount := ctx.typeCount
  let callee ← try
      pure (.ok (← InstanceReader.read catalog typeCount (← catalog.field input "constant_query_context" path) path))
    catch reason => pure (.error reason)
  let values ← catalog.array (← catalog.field input "source_scopes" path) path
  let scopes ← values.mapIdxM fun index input => do
    try pure (.ok (← scope catalog typeCount values.size index input s!"{path}.source_scopes[{index}]"))
    catch reason => pure (.error reason)
  let required ← try pure (.ok (← requiredConstants catalog ctx input path))
    catch reason => pure (.error reason)
  let spans ← try pure (.ok (← backtraceSpans catalog input path))
    catch reason => pure (.error reason)
  return ⟨callee,scopes,required,← callSites catalog input path,spans⟩

end Miri.Input.Reader.BodyMetadataReader
