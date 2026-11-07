import Miri.Input.Model.Types

namespace Miri.Input

private instance : Inhabited TypedValue := ⟨.scalar .null⟩

private partial def eraseChecked (value : TypedValue (.checked program body)) : TypedValue :=
  match value with
  | .scalar value => .scalar value
  | .diagnostic value => .diagnostic value
  | .array values => .array (values.map eraseChecked)
  | .object fields => .object (fields.map fun (key, value) => (key, eraseChecked value))
  | .typeRef id => .typeRef id.val
  | .allocationRef id => .allocationRef id.val
  | .instanceRef id => .instanceRef id.val
  | .localRef id => .localRef id.val
  | .blockRef id => .blockRef id.val
  | .sourceSpan value => .sourceSpan value
  | .sourceInfo value => .sourceInfo value
  | .statement variant status fields => .statement variant status (fields.map fun (key,value) => (key,eraseChecked value))
  | .terminator variant status fields => .terminator variant status (fields.map fun (key,value) => (key,eraseChecked value))
  | .rvalue variant status fields => .rvalue variant status (fields.map fun (key,value) => (key,eraseChecked value))
  | .binOperator op status => .binOperator op status
  | .unknownBinOperator tag status => .unknownBinOperator tag status
  | .unOperator op status => .unOperator op status
  | .unknownUnOperator tag status => .unknownUnOperator tag status
  | .enumTag category tag fields => .enumTag category tag (fields.map fun (key,value) => (key,eraseChecked value))
  | .userTypeProjection value => .userTypeProjection value
  | .operand variant status fields => .operand variant status (fields.map fun (key,value) => (key,eraseChecked value))
  | .projection variant fields => .projection variant (fields.map fun (key,value) => (key,eraseChecked value))

def TypedValue.toRaw {context : ReferenceContext} (value : TypedValue context) : TypedValue :=
  match context with
  | .raw => value
  | .checked _ _ => eraseChecked value

def LocalDecl.typeIdNat (decl : LocalDecl context) : Nat := ReferenceContext.toNat (context := context) (kind := .type) decl.typeId

def LocalDecl.toRaw (decl : LocalDecl context) : LocalDecl :=
  ⟨decl.id, decl.typeIdNat, decl.sourceInfo, decl.payload⟩

def MirNode.toRaw (node : MirNode context) : MirNode := ⟨node.value.toRaw, node.sourceInfo⟩

def BasicBlock.toRaw (block : BasicBlock context) : BasicBlock :=
  ⟨block.id, block.statements.map MirNode.toRaw, block.terminator.toRaw, block.cleanup, block.payload⟩

def BodyCore.rawLocals (body : BodyCore) : Array LocalDecl := body.locals.map LocalDecl.toRaw

def BodyCore.rawBlocks (body : BodyCore) : Array BasicBlock := body.blocks.map BasicBlock.toRaw

def BodyCore.spreadArgumentNat (body : BodyCore) : Option Nat :=
  body.spreadArgument.map (ReferenceContext.toNat (context := body.context) (kind := .local))

@[simp] theorem BodyCore.rawLocals_size (body : BodyCore) : body.rawLocals.size = body.locals.size := by
  simp [rawLocals]

@[simp] theorem BodyCore.rawBlocks_size (body : BodyCore) : body.rawBlocks.size = body.blocks.size := by
  simp [rawBlocks]

theorem BodyCore.checked_locals_size (body : BodyCore) (program : ProgramShape) (scope : BodyShape)
    (checked : body.context = .checked program scope) : body.locals.size = scope.locals := by
  have aligned := body.aligned
  generalize localsCount : body.locals.size = countLocals at aligned
  generalize blocksCount : body.blocks.size = countBlocks at aligned
  rw [checked] at aligned
  simpa [localsCount] using aligned.1

theorem BodyCore.checked_blocks_size (body : BodyCore) (program : ProgramShape) (scope : BodyShape)
    (checked : body.context = .checked program scope) : body.blocks.size = scope.blocks := by
  have aligned := body.aligned
  generalize localsCount : body.locals.size = countLocals at aligned
  generalize blocksCount : body.blocks.size = countBlocks at aligned
  rw [checked] at aligned
  simpa [blocksCount] using aligned.2

end Miri.Input
