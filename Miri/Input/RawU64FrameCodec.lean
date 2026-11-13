import Miri.Input.CtfeMirSource
import Miri.Input.GenericMaterialCodec
import Miri.Input.MirTemplate

namespace Miri.Input.RawU64FrameCodec
open Lean RawU64Frame CtfeMirSource
private def keys (value : Json) (expected : List String) : Except String Unit := do
  let actual := (← value.getObj?).toArray.map (·.1)
  unless actual.size == expected.length && actual.all expected.contains do throw "raw u64 source field set mismatch"
private def field (value : Json) (key : String) := value.getObjVal? key
private def text (value : Json) (key : String) := (field value key).bind Json.getStr?
private def nat (value : Json) (key : String) := (field value key).bind Json.getNat?
private def sourceInfo (value : Json) : Except String MIR.SourceInfo := do
  keys value ["span","scope"]
  pure ⟨⟨← nat value "span"⟩,← nat value "scope"⟩
private def u64Shape (value : Json) : Except String Unit := do
  keys value ["kind","bits"]
  unless (← text value "kind") == "uint" && (← nat value "bits") == 64 do throw "raw type-const source requires u64"
private def reference (value : Json) : Except String Reference := do
  keys value ["kind","definition","arguments","declared_type","promoted","span","user_type"]
  unless (← text value "kind") == "unevaluated" && (← field value "promoted") == .null &&
      (← field value "user_type") == .null do throw "raw u64 source constant reference policy mismatch"
  u64Shape (← field value "declared_type")
  let arguments ← (← (← field value "arguments").getArr?).mapM (GenericMaterialCodec.readTerm 16384)
  for argument in arguments do
    unless argument.sort != .aggregate do throw "raw u64 constant has aggregate generic argument"
    MirTemplate.validateClosed 16384 argument
  pure ⟨← GenericMaterialCodec.readDefinition (← field value "definition"),arguments,⟨← nat value "span"⟩,none⟩
private def localPlace (locals : Nat) (value : Json) : Except String Nat := do
  keys value ["local","fields"]
  unless (← (← field value "fields").getArr?).isEmpty do throw "raw u64 source has projected local"
  let slot ← nat value "local"
  unless slot < locals do throw "raw u64 source local out of bounds"
  pure slot
private def operand (locals : Nat) (value : Json) : Except String Operand := do
  match ← text value "kind" with
  | "copy" | "move" =>
    keys value ["kind","place"]
    let slot ← localPlace locals (← field value "place")
    pure (if (← text value "kind") == "copy" then .copy slot else .move slot)
  | "constant" => keys value ["kind","source"]; .constant <$> reference (← field value "source")
  | "source_value" =>
    keys value ["kind","source_class","span","user_type","value"]
    unless #["type_value","literal_value"].contains (← text value "source_class") &&
        (← field value "user_type") == .null do throw "raw u64 source literal annotation/class mismatch"
    let span ← nat value "span"
    let literal ← field value "value"
    keys literal ["kind","bits","value"]
    unless (← text literal "kind") == "uint" && (← nat literal "bits") == 64 do throw "raw u64 literal type mismatch"
    let some bits := (← text literal "value").toNat? | throw "raw u64 literal integer malformed"
    unless bits < 2^64 do throw "raw u64 literal overflows"
    let kind := if (← text value "source_class") == "type_value" then ValueClass.typeValue else .literalValue
    pure (.sourceValue ⟨kind,⟨span⟩,none,UInt64.ofNat bits⟩)
  | _ => throw "raw u64 source operand unsupported"
private def expression (locals : Nat) (value : Json) : Except String Rvalue := do
  match ← text value "kind" with
  | "use" =>
    keys value ["kind","operand","retag"]
    let retag ← match ← text value "retag" with | "yes" => pure true | "no" => pure false | _ => throw "raw u64 retag malformed"
    pure (.use (← operand locals (← field value "operand")) retag)
  | "unary" =>
    keys value ["kind","op","operand"]
    unless (← text value "op") == "not" do throw "raw u64 unary operation unsupported"
    .unaryNot <$> operand locals (← field value "operand")
  | _ => throw "raw u64 expression unsupported"
private def instruction (locals : Nat) (value : Json) : Except String Statement := do
  match ← text value "kind" with
  | "assign" =>
    keys value ["kind","destination","value"]
    pure (.assign (← localPlace locals (← field value "destination")) (← expression locals (← field value "value")))
  | "storage_live" | "storage_dead" =>
    keys value ["kind","local"]
    let slot ← nat value "local"
    unless slot > 0 && slot < locals do throw "raw u64 storage local out of bounds"
    pure (if (← text value "kind") == "storage_live" then .live slot else .dead slot)
  | "nop" => keys value ["kind"]; pure .nop
  | "const_eval_counter" => keys value ["kind"]; pure .counter
  | _ => throw "raw u64 source statement unsupported"

private def scope (value : Json) : Except String Scope := do
  keys value ["span","parent","lint_root"]
  let parent ← field value "parent"
  let parent ← if parent == .null then pure none else some <$> parent.getNat?
  let lint ← field value "lint_root"
  let lint ← if lint == .null then pure none else do
    keys lint ["owner","local_id"]
    pure (some (⟨← GenericMaterialCodec.readDefinition (← field lint "owner"),← nat lint "local_id"⟩ : LintRoot))
  pure ⟨⟨← nat value "span"⟩,parent,lint⟩

/-- Complete typed source/header decoder. No source preamble, class, span,
mutability, scope or retag flag is discarded by the u64 policy. -/
def read (value : Json) : Except String Source := do
  keys value ["definition","owner_kind","def_path","preamble_def_span","source_role","promoted","policy","phase","environment_recipe","parameters",
    "user_type_annotations","required_consts","span","arg_count","spread_arg","locals","blocks","source_scopes"]
  let definition ← GenericMaterialCodec.readDefinition (← field value "definition")
  unless (← text value "policy") == "u64_physical_constants_v1" && (← text value "source_role") == "ctfe" &&
      (← text value "phase") == "runtime_post_cleanup" && (← field value "promoted") == .null &&
      (← nat value "arg_count") == 0 && (← field value "spread_arg") == .null &&
      (← (← field value "parameters").getArr?).isEmpty &&
      (← (← field value "user_type_annotations").getArr?).isEmpty do throw "raw u64 source header policy mismatch"
  let environment ← field value "environment_recipe"
  keys environment ["kind","owner","mode"]
  unless (← text environment "kind") == "declaration" && (← text environment "mode") == "post_analysis" &&
      (← GenericMaterialCodec.readDefinition (← field environment "owner")) == definition do throw "raw u64 source declaration environment mismatch"
  let locals ← (← (← field value "locals").getArr?).mapM fun slot => do
    keys slot ["type","source","mutable"]
    u64Shape (← field slot "type")
    pure (← sourceInfo (← field slot "source"),← (← field slot "mutable").getBool?)
  let blocks ← (← field value "blocks").getArr?
  let some block := blocks[0]? | throw "raw u64 source block absent"
  unless blocks.size == 1 do throw "raw u64 source requires one block"
  keys block ["cleanup","statements","terminator"]
  unless !(← (← field block "cleanup").getBool?) do throw "raw u64 source cleanup block unsupported"
  let statements ← (← (← field block "statements").getArr?).mapM fun statement => do
    keys statement ["source","kind"]
    pure (← instruction locals.size (← field statement "kind"),← sourceInfo (← field statement "source"))
  let terminator ← field block "terminator"
  keys terminator ["source","kind"]
  let kind ← field terminator "kind"
  keys kind ["kind"]
  unless (← text kind "kind") == "return" do throw "raw u64 source terminator unsupported"
  let ownerKind ← match ← text value "owner_kind" with
    | "const" => pure OwnerKind.constant
    | "associated_const" => pure .associatedConstant
    | "anon_const" => pure .anonymousConstant
    | _ => throw "raw u64 source owner kind unsupported"
  let program : RawU64Frame.Program := {
    ownerKind
    defPath := ← text value "def_path"
    preambleDefSpan := ⟨← nat value "preamble_def_span"⟩
    localCount := locals.size
    required := ← (← (← field value "required_consts").getArr?).mapM reference
    statements := statements.map (·.1) }
  let source : Source := {
    definition,role := .ctfe,promoted := none,policy := .rawU64,phase := .Runtime .PostCleanup,
    environment := .declaration definition .postAnalysis,parameters := #[],
    -- Only legacy scalar policies use this field; the physical typed preamble
    -- is retained intact in program.required and consumed by the new provider.
    requiredConstants := #[],span := ⟨← nat value "span"⟩,program := .rawU64 program,
    localSources := locals.map (·.1),localMutability := locals.map (·.2),
    statementSources := #[statements.map (·.2)],terminatorSources := #[← sourceInfo (← field terminator "source")],
    scopes := ← (← (← field value "source_scopes").getArr?).mapM scope }
  CtfeMirSource.validate source
  pure source
end Miri.Input.RawU64FrameCodec
