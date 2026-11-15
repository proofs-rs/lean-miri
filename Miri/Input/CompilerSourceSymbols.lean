import Miri.Input.SourceCompilerWorld

/-! Pure symbol spelling and symbolic Item keys from declaration attributes.
No function body, ABI, winner, or numeric CallInstance is synthesized here. -/
namespace Miri.Input.CompilerSourceSymbols
open Lean

/-- Pinned symbol_name_from_attrs precedence: std-internal namespace first,
then export_name, then no_mangle. Proc-macro and non-ASCII internal mangling
require additional source rules and remain explicitly unsupported. -/
def symbolFromAttributes (namespacePrefix : String) (attributes : SourceSymbols.Attributes) : Except String String := do
  unless !attributes.procMacroDeclarations do throw "proc-macro declaration symbol source rule unsupported"
  if attributes.stdInternalSymbol then
    unless namespacePrefix.startsWith "_RNvC" && namespacePrefix.endsWith "7___rustc" do
      throw "invalid source internal-symbol namespace"
    let name ← match attributes.symbolName, attributes.itemName with
      | some name, _ | none, some name => pure name
      | none, none => throw "internal symbol source name absent"
    unless name.toList.all (fun c => c == '_' || ('a' ≤ c && c ≤ 'z') ||
        ('A' ≤ c && c ≤ 'Z') || ('0' ≤ c && c ≤ '9')) do
      throw "internal symbol source identifier encoding unsupported"
    let separator := match name.toList.head? with
      | some c => if c == '_' || ('0' ≤ c && c ≤ '9') then "_" else ""
      | none => ""
    return namespacePrefix ++ toString name.utf8ByteSize ++ separator ++ name
  if let some name := attributes.symbolName then return name
  if attributes.noMangle then
    let some name := attributes.itemName | throw "no-mangle source item name absent"
    return name
  throw "source declaration has no explicit symbol attribute"

/-- Export candidates and actual foreign declarations share the same fixed
attribute spelling rule; traversal/winner metadata does not affect spelling. -/
def symbol (namespacePrefix : String) (declaration : SourceSymbols.Declaration) : Except String String :=
  symbolFromAttributes namespacePrefix declaration.attributes

/-- Instance::mono erases lifetime slots and cannot invent type/const arguments.
Called only for the selected function declaration, never during clash lookup. -/
def monoKey (declaration : SourceSymbols.Declaration) : Except String SourceCompilerWorld.InstanceKey := do
  let arguments ← declaration.parameters.mapM fun parameter => do
    match parameter with
    | .region => pure (MIR.GenericArg.Lifetime .Erased)
    | .typeParameter | .constParameter => throw "exported Item requires missing type/const arguments"
  return { definition := declaration.definition, arguments }

/-- The shared World consumes this source identity header only at actual demand. -/
def itemDeclaration (declaration : SourceSymbols.Declaration) : Except String SourceCompilerWorld.ItemDeclaration := do
  let kind : SourceCompilerWorld.ItemKind ← match declaration.kind with
    | "function" => pure .function
    | "associated_function" => pure .associatedFunction
    | _ => throw "exported source declaration is not callable"
  return { definition := declaration.definition, path := declaration.path, kind, parameters := declaration.parameters }

end Miri.Input.CompilerSourceSymbols
