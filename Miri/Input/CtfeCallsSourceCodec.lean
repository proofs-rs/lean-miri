import Miri.Input.CtfeMirSource
import Miri.Input.GenericMaterialCodec

namespace Miri.Input.CtfeCallsSourceCodec
open Lean CtfeMirSource Miri.Interpreter.CompileTime.CallFrame
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
private def localDefinition (value : Json) : Except String Nat := do
  let definition ← GenericMaterialCodec.readDefinition value
  unless definition.crateIndex == 0 do throw "calls policy requires local crate0 source identity"
  pure definition.index
private def reference (value : Json) : Except String Reference := do
  if (← text value "kind") == "parameter_constant" then
    keys value ["kind","index","declared_type","span","user_type"]
    return .parameterConstant (← nat value "index") (← optionalNat (← field value "user_type"))
      (← shape 16384 (← field value "declared_type")) (← nat value "span")
  keys value ["kind","definition","promoted","arguments","parameter","declared_type","span","user_type"]
  unless (← field value "promoted") == .null do throw "promoted calls references unsupported"
  let arguments ← arr value "arguments"
  let definition ← localDefinition (← field value "definition")
  let annotation ← optionalNat (← field value "user_type")
  let ty ← shape 16384 (← field value "declared_type")
  let location ← nat value "span"
  match ← text value "kind" with
  | "direct" =>
    unless (← field value "parameter") == .null && arguments.isEmpty do throw "direct constant has type arguments"
    pure (.direct definition annotation ty location)
  | "associated" =>
    let parameter ← nat value "parameter"
    let #[argument] := arguments | throw "associated source requires exactly one type-parameter argument"
    keys argument ["kind","index"]
    unless (← text argument "kind") == "type_parameter" && (← nat argument "index") == parameter do
      throw "associated source argument tree contradicts parameter reference"
    pure (.associated definition parameter annotation ty location)
  | _ => throw "unknown raw constant reference kind"
private def operand (value : Json) : Except String Operand := do
  match ← text value "kind" with
  | "copy" => keys value ["kind","place"]; pure (.copy (← place (← field value "place")))
  | "move" => keys value ["kind","place"]; pure (.move (← place (← field value "place")))
  | "constant" =>
    keys value ["kind","source"]
    pure (.constant (← reference (← field value "source")))
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
      | "sub_with_overflow" => pure .subWithOverflow
      | "eq" => pure .eq | "div" => pure .div | _ => throw "unsupported raw CTFE binary operator"
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
  if (← text value "kind") == "division_by_zero" then
    keys value ["kind","operand"]
    return .divisionByZero (← operand (← field value "operand"))
  keys value ["kind","op","left","right"]
  unless (← text value "kind") == "overflow" do throw "unsupported raw CTFE assertion message"
  let kind ← match ← text value "op" with
    | "add" => pure OverflowKind.add | "sub" => pure .sub
    | _ => throw "unsupported raw CTFE overflow diagnostic operator"
  pure (.overflow kind (← operand (← field value "left")) (← operand (← field value "right")))
private def terminator (value : Json) : Except String Terminator := do
  match ← text value "kind" with
  | "resume" => keys value ["kind"]; pure .resume
  | "call" =>
    keys value ["kind","callee","type_arguments","arguments","destination","target","unwind","fn_span","function_operand_span","function_source_class","argument_spans","call_source","function_user_type","abi","track_caller"]
    let unwind ← field value "unwind"
    let unwind ← match ← text unwind "kind" with
      | "unreachable" => keys unwind ["kind"]; pure Unwind.unreachable
      | "cleanup" => keys unwind ["kind","target"]; pure (.cleanup (← nat unwind "target"))
      | _ => throw "unsupported calls unwind action"
    pure (.call {
      callee := ← localDefinition (← field value "callee")
      typeArguments := ← (← arr value "type_arguments").mapM localDefinition
      arguments := ← (← arr value "arguments").mapM operand
      destination := ← place (← field value "destination"),target := ← nat value "target",unwind
      functionSpan := ← nat value "fn_span"
      functionOperandSpan := ← nat value "function_operand_span"
      functionSourceClass := ← match ← text value "function_source_class" with
        | "literal_value" => pure SourceValueKind.literalValue
        | "type_value" => pure .typeValue
        | _ => throw "unknown FnDef raw source class"
      argumentSpans := ← (← arr value "argument_spans").mapM Json.getNat?
      callSource := ← text value "call_source"
      functionUserType := ← optionalNat (← field value "function_user_type")
      abi := ← text value "abi",trackCaller := ← bool value "track_caller"})
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
  let constArgs := (← text value "policy") == "scalar_u32_const_args_v1"
  keys value (["definition","source_role","promoted","policy","phase","environment_recipe",
    "parameters","required_consts","span","arg_count","spread_arg","locals","blocks","source_scopes","user_type_annotations"] ++ if constArgs then ["constant_parameter_types"] else [])
  let definition ← GenericMaterialCodec.readDefinition (← field value "definition")
  let role ← match ← text value "source_role" with
    | "ctfe" => pure CompilerBodyRole.ctfe | "runtime" => pure .runtime
    | _ => throw "unknown raw CTFE compiler body role"
  let policy ← match ← text value "policy" with
    | "scalar_u32_calls_v1" => pure Policy.scalarU32CallsV1
    | "scalar_u32_const_args_v1" => pure .scalarU32ConstArgsV1 | _ => throw "unknown raw CTFE source policy"
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
    let cleanup ← bool value "cleanup"
    let statements ← (← arr value "statements").mapM fun value => do
      keys value ["source","kind"]
      pure (← statement (← field value "kind"),← info (← field value "source"))
    let term ← field value "terminator"
    keys term ["source","kind"]
    pure ((⟨statements.map (·.1),← terminator (← field term "kind")⟩ : Block),
      statements.map (·.2),← info (← field term "source"),cleanup)
  unless (← arr value "user_type_annotations").isEmpty do throw "PostCleanup annotation table must be cleared"
  let parameters ← (← arr value "parameters").mapM GenericMaterialCodec.readSort
  let required ← (← arr value "required_consts").mapM reference
  let constantParameters ← if constArgs then (← arr value "constant_parameter_types").mapM fun item => do
    keys item ["index","type"]
    pure ({index := ← nat item "index",ty := ← shape 16384 (← field item "type")} : ConstantParameter)
    else pure #[]
  let program : Miri.Interpreter.CompileTime.SourceStack.Source := {
    definition := ← localDefinition (← field value "definition"),name := ""
    required,constantParameters,typeParameters := if constArgs then 0 else parameters.size
    cleanup := blocks.map (·.2.2.2)
    program := ⟨locals.map (·.1),← nat value "arg_count",blocks.map (·.1)⟩ }
  let source : Source := {
    definition,role,promoted := ← optionalNat (← field value "promoted"),policy,phase := .Runtime .PostCleanup
    environment := .declaration owner .postAnalysis
    parameters
    requiredConstants := #[]
    span := ⟨← nat value "span"⟩
    program := .calls program
    localSources := locals.map (·.2.1),localMutability := locals.map (·.2.2)
    statementSources := blocks.map (·.2.1),terminatorSources := blocks.map (·.2.2.1)
    scopes := ← (← arr value "source_scopes").mapM scope }
  validate source
  pure source
end Miri.Input.CtfeCallsSourceCodec
