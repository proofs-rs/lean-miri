import Miri.Input.Reader.Statements

namespace Miri.Input.Reader.InlineAsmReader
open Lean Miri.MIR
abbrev Decode := MIRReader.Decode

def span (catalog : Catalog) (input : Json) (path : String) : Decode SpanRef :=
  ConstantReader.span catalog input path

private def arch (input : String) : Except String InlineAsmArch :=
  match input with
  | "X86" => pure .X86 | "X86_64" => pure .X86_64
  | "Arm" => pure .Arm | "Arm64EC" => pure .Arm64EC | "AArch64" => pure .AArch64
  | "Amdgpu" => pure .Amdgpu | "RiscV32" => pure .RiscV32 | "RiscV64" => pure .RiscV64
  | "Nvptx64" => pure .Nvptx64 | "PowerPC" => pure .PowerPC | "PowerPC64" => pure .PowerPC64
  | "Hexagon" => pure .Hexagon | "LoongArch32" => pure .LoongArch32 | "LoongArch64" => pure .LoongArch64
  | "Mips" => pure .Mips | "Mips64" => pure .Mips64 | "Xtensa" => pure .Xtensa
  | "S390x" => pure .S390x | "Sparc" => pure .Sparc | "Sparc64" => pure .Sparc64
  | "SpirV" => pure .SpirV | "Wasm32" => pure .Wasm32 | "Wasm64" => pure .Wasm64
  | "Bpf" => pure .Bpf | "Avr" => pure .Avr | "Msp430" => pure .Msp430
  | "M68k" => pure .M68k | "CSKY" => pure .CSky
  | name => throw s!"unsupported assembly architecture {name}"

private def register (catalog : Catalog) (input : Json) (path : String) : Except String InlineAsmRegOrRegClass := do
  let arch ← arch (← catalog.string (← catalog.field input "arch" path) path)
  let name ← catalog.string (← catalog.field input "name" path) path
  match ← catalog.string (← catalog.field input "kind" path) path with
  | "register" => return .Reg arch name
  | "register_class" => return .RegClass arch name
  | kind => throw s!"{path}: unsupported assembly register kind {kind}"

private def piece (catalog : Catalog) (input : Json) (path : String) : Decode InlineAsmTemplatePiece := do
  let field := fun key => catalog.field input key path
  match ← catalog.string (← field "kind") path with
  | "string" => return .String (← catalog.string (← field "text") path)
  | "placeholder" =>
    let modifier ← catalog.inspect (← field "modifier") path
    let modifier ← if modifier == .null then pure none else do
      let text ← catalog.string modifier path
      match text.toList with
      | [char] => pure (some char)
      | _ => throw s!"{path}: assembly modifier must be one character"
    return .Placeholder (← catalog.natural (← field "operand_index") path) modifier
      (← span catalog (← field "span") path)
  | kind => throw s!"{path}: unsupported assembly template piece {kind}"

private def optionalPlace (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode (Option PlaceId) := do
  let value ← catalog.inspect input path
  if value == .null then return none
  return some (← OperandReader.place catalog ctx.typeCount input path)

private def operand (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode InlineAsmOperandNode := do
  let field := fun key => catalog.field input key path
  let register := do register catalog (← field "register") path
  let constant : Decode ConstantId := do
    return ⟨← ConstantReader.constant catalog ctx (← field "value") path⟩
  match ← catalog.string (← field "kind") path with
  | "in" => return .In (← register) (← OperandReader.operand catalog ctx (← field "value") path)
  | "out" =>
    return .Out (← register) (← catalog.boolean (← field "late") path)
      (← optionalPlace catalog ctx (← field "place") path)
  | "inout" =>
    return .InOut (← register) (← catalog.boolean (← field "late") path)
      (← OperandReader.operand catalog ctx (← field "input") path)
      (← optionalPlace catalog ctx (← field "output") path)
  | "const" => return .Const (← constant)
  | "sym_fn" => return .SymFn (← constant)
  | "sym_static" => return .SymStatic (← GenericReader.definition catalog (← field "def_id") path)
  | "label" => return .Label (← catalog.natural (← field "target_index") path)
  | kind => throw s!"{path}: unsupported assembly operand {kind}"

def read (catalog : Catalog) (ctx : ConstantReader.Context) (input : Json) (path : String) : Decode InlineAsmNode := do
  let field := fun key => catalog.field input key path
  let macroKind ← match ← catalog.string (← field "asm_macro") path with
    | "asm" => pure InlineAsmMacro.Asm
    | "naked_asm" => pure .NakedAsm
    | kind => throw s!"{path}: unsupported assembly macro {kind}"
  let options ← field "options"
  let option := fun key => do catalog.boolean (← catalog.field options key path) path
  let options : InlineAsmOptions := ⟨← option "pure", ← option "nomem", ← option "readonly",
    ← option "preserves_flags", ← option "noreturn", ← option "nostack", ← option "att_syntax",
    ← option "raw", ← option "may_unwind"⟩
  let template ← (← catalog.array (← field "template") path).mapIdxM fun index input =>
    piece catalog input s!"{path}.template[{index}]"
  let operands ← (← catalog.array (← field "operands") path).mapIdxM fun index input =>
    operand catalog ctx input s!"{path}.operands[{index}]"
  let spans ← (← catalog.array (← field "line_spans") path).mapIdxM fun index input =>
    span catalog input s!"{path}.line_spans[{index}]"
  let targets ← (← catalog.array (← field "targets") path).mapM fun input => catalog.natural input path
  for operand in operands do
    if let .Label index := operand then
      unless index < targets.size do throw s!"{path}: assembly label exceeds target list"
  for piece in template do
    if let .Placeholder index _ _ := piece then
      unless index < operands.size do throw s!"{path}: assembly placeholder exceeds operand list"
  return ⟨macroKind, template, operands, options, spans, targets, ← catalog.unwind (← field "unwind") path⟩

end Miri.Input.Reader.InlineAsmReader
