import Miri.Input.CtfeMirSource
import Miri.Input.GenericMaterialCodec
import Miri.Input.CtfeCallsSourceCodec
import Miri.Input.RawU64FrameCodec

namespace Miri.Input.CtfeMirSourceCodec
open Lean CtfeMirSource Miri.Interpreter.CompileTime.ScalarFrame
private def keys (value : Json) (allowed : List String) : Except String Unit := do
  for (key,_) in (← value.getObj?).toArray do
    unless allowed.contains key do throw s!"unknown raw CTFE source field {key}"
private def field (value : Json) (name : String) := value.getObjVal? name
private def nat (value : Json) (name : String) : Except String Nat := do (← field value name).getNat?
private def text (value : Json) (name : String) : Except String String := do (← field value name).getStr?
private def arr (value : Json) (name : String) : Except String (Array Json) := do (← field value name).getArr?
private def bool (value : Json) (name : String) : Except String Bool := do (← field value name).getBool?
private def optionalNat (value : Json) : Except String (Option Nat) :=
  if value == .null then pure none else some <$> value.getNat?
private def decimal (value : Json) (name : String) : Except String Nat := do
  let value ← text value name
  let some number := value.toNat? | throw "invalid raw CTFE decimal source scalar"
  pure number
private def info (value : Json) : Except String Miri.MIR.SourceInfo := do
  keys value ["span","scope"]
  pure ⟨⟨← nat value "span"⟩,← nat value "scope"⟩
private def shape : Nat → Json → Except String Ty
  | 0,_ => throw "raw CTFE type traversal exhausted"
  | fuel+1,value => do
    match ← text value "kind" with
    | "uint" => keys value ["kind","bits"]; pure (.uint (← nat value "bits"))
    | "boolean" => keys value ["kind"]; pure .boolean
    | "unit" => keys value ["kind"]; pure .unit
    | "never" => keys value ["kind"]; pure .never
    | "pair" =>
      keys value ["kind","left","right"]
      pure (.pair (← shape fuel (← field value "left")) (← shape fuel (← field value "right")))
    | _ => throw "unsupported raw CTFE source type"
private def place (value : Json) : Except String Place := do
  keys value ["local","fields"]
  pure ⟨← nat value "local",← (← arr value "fields").mapM Json.getNat?⟩
private def literal (value : Json) : Except String Value := do
  match ← text value "kind" with
  | "uint" =>
    keys value ["kind","bits","value"]
    pure (.uint (← nat value "bits") (← decimal value "value"))
  | "boolean" => keys value ["kind","value"]; pure (.boolean (← bool value "value"))
  | "unit" => keys value ["kind"]; pure .unit
  | _ => throw "raw CTFE source value is not a primitive source constructor"
private def operand (value : Json) : Except String Operand := do
  match ← text value "kind" with
  | "copy" => keys value ["kind","place"]; pure (.copy (← place (← field value "place")))
  | "move" => keys value ["kind","place"]; pure (.move (← place (← field value "place")))
  | "source_value" =>
    keys value ["kind","source_class","span","user_type","value"]
    let kind ← match ← text value "source_class" with
      | "type_value" => pure SourceValueKind.typeValue
      | "literal_value" => pure .literalValue
      | _ => throw "unknown raw CTFE source value class"
    pure (.sourceValue ⟨kind,← nat value "span",← optionalNat (← field value "user_type"),← literal (← field value "value")⟩)
  | _ => throw "unsupported raw CTFE source operand"
private def rvalue (value : Json) : Except String Rvalue := do
  match ← text value "kind" with
  | "use" =>
    keys value ["kind","operand","retag"]
    let retag ← match ← text value "retag" with
      | "yes" => pure true | "no" => pure false | _ => throw "unknown raw CTFE retag policy"
    pure (.use (← operand (← field value "operand")) retag)
  | "binary" =>
    keys value ["kind","op","left","right"]
    let kind ← match ← text value "op" with
      | "gt" => pure Binary.gt | "add_with_overflow" => pure .addWithOverflow
      | "sub_with_overflow" => pure .subWithOverflow | _ => throw "unsupported raw CTFE binary operator"
    pure (.binary kind (← operand (← field value "left")) (← operand (← field value "right")))
  | _ => throw "unsupported raw CTFE source rvalue"
private def statement (value : Json) : Except String Statement := do
  match ← text value "kind" with
  | "assign" =>
    keys value ["kind","destination","value"]
    pure (.assign (← place (← field value "destination")) (← rvalue (← field value "value")))
  | "storage_live" => keys value ["kind","local"]; pure (.live (← nat value "local"))
  | "storage_dead" => keys value ["kind","local"]; pure (.dead (← nat value "local"))
  | "const_eval_counter" => keys value ["kind"]; pure .counter
  | "nop" => keys value ["kind"]; pure .nop
  | _ => throw "unsupported raw CTFE source statement"
private def message (value : Json) : Except String AssertMessage := do
  keys value ["kind","op","left","right"]
  unless (← text value "kind") == "overflow" do throw "unsupported raw CTFE assertion message"
  let kind ← match ← text value "op" with
    | "add" => pure OverflowKind.add | "sub" => pure .sub
    | _ => throw "unsupported raw CTFE overflow diagnostic operator"
  pure (.overflow kind (← operand (← field value "left")) (← operand (← field value "right")))
private def terminator (value : Json) : Except String Terminator := do
  match ← text value "kind" with
  | "goto" => keys value ["kind","target"]; pure (.goto (← nat value "target"))
  | "switch" =>
    keys value ["kind","operand","cases","otherwise"]
    let cases ← (← arr value "cases").mapM fun value => do
      keys value ["value","target"]
      pure (← decimal value "value",← nat value "target")
    pure (.switch (← operand (← field value "operand")) cases (← nat value "otherwise"))
  | "assert" =>
    keys value ["kind","condition","expected","message","target","unwind"]
    unless (← text value "unwind") == "unreachable" do throw "raw CTFE source unwind policy unsupported"
    pure (.assert (← operand (← field value "condition")) (← bool value "expected")
      (← message (← field value "message")) (← nat value "target"))
  | "return" => keys value ["kind"]; pure .ret
  | _ => throw "unsupported raw CTFE source terminator"
private def scope (value : Json) : Except String Scope := do
  keys value ["span","parent","lint_root"]
  let raw ← field value "lint_root"
  let lintRoot ← if raw == .null then pure none else do
    keys raw ["owner","local_id"]
    pure (some ⟨← GenericMaterialCodec.readDefinition (← field raw "owner"),← nat raw "local_id"⟩)
  pure ⟨⟨← nat value "span"⟩,← optionalNat (← field value "parent"),lintRoot⟩

def read (value : Json) : Except String Source := do
  if (text value "policy").toOption == some "u64_physical_constants_v1" then
    return ← RawU64FrameCodec.read value
  if (text value "policy").toOption == some "scalar_u32_calls_v1" ||
      (text value "policy").toOption == some "scalar_u32_const_args_v1" then
    return ← CtfeCallsSourceCodec.read value
  keys value ["definition","source_role","promoted","policy","phase","environment_recipe",
    "parameters","required_consts","span","arg_count","spread_arg","locals","blocks","source_scopes"]
  let definition ← GenericMaterialCodec.readDefinition (← field value "definition")
  let role ← match ← text value "source_role" with
    | "ctfe" => pure CompilerBodyRole.ctfe | "runtime" => pure .runtime
    | _ => throw "unknown raw CTFE compiler body role"
  let policy ← match ← text value "policy" with
    | "scalar_u32" => pure Policy.scalarU32 | _ => throw "unknown raw CTFE source policy"
  unless (← text value "phase") == "runtime_post_cleanup" do throw "unsupported raw CTFE source phase"
  unless (← field value "spread_arg") == .null do throw "raw CTFE scalar frame cannot have a spread argument"
  let recipe ← field value "environment_recipe"
  keys recipe ["kind","owner","mode"]
  unless (← text recipe "kind") == "declaration" && (← text recipe "mode") == "post_analysis" do
    throw "unsupported CTFE source declaration environment recipe"
  let owner ← GenericMaterialCodec.readDefinition (← field recipe "owner")
  let locals ← (← arr value "locals").mapM fun value => do
    keys value ["type","source","mutable"]
    pure (← shape 16384 (← field value "type"),← info (← field value "source"),← bool value "mutable")
  let blocks ← (← arr value "blocks").mapM fun value => do
    keys value ["cleanup","statements","terminator"]
    unless !(← bool value "cleanup") do throw "CTFE scalar frame cleanup source unsupported"
    let statements ← (← arr value "statements").mapM fun value => do
      keys value ["source","kind"]
      pure (← statement (← field value "kind"),← info (← field value "source"))
    let term ← field value "terminator"
    keys term ["source","kind"]
    pure ((⟨statements.map (·.1),← terminator (← field term "kind")⟩ : Block),
      statements.map (·.2),← info (← field term "source"))
  let source : Source := {
    definition,role,promoted := ← optionalNat (← field value "promoted"),policy,phase := .Runtime .PostCleanup
    environment := .declaration owner .postAnalysis
    parameters := ← (← arr value "parameters").mapM GenericMaterialCodec.readSort
    requiredConstants := ← (← arr value "required_consts").mapM operand
    span := ⟨← nat value "span"⟩
    program := .scalar ⟨locals.map (·.1),← nat value "arg_count",blocks.map (·.1)⟩
    localSources := locals.map (·.2.1),localMutability := locals.map (·.2.2)
    statementSources := blocks.map (·.2.1),terminatorSources := blocks.map (·.2.2)
    scopes := ← (← arr value "source_scopes").mapM scope }
  validate source
  pure source
end Miri.Input.CtfeMirSourceCodec
