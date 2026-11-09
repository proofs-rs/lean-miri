import Lean.Elab.Deriving.ToExpr
import Miri.Input

/-! Elaboration-time input reflection. Generated declarations contain typed
constructor values, not an opaque call to the IO decoder. This front end is
part of the input trust boundary; importing data does not establish safety. -/
namespace Miri.Frontend
open Lean

/-- Extract only with a kernel-checked witness of success. No default value. -/
@[noinline] def checkedSome {α : Type} (value : Option α) (success : value.isSome = true) : α :=
  value.get success

private def trueRefl : Expr :=
  mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (toExpr true)

@[noinline] def checkedAllocId (value : UInt64)
    (success : (Memory.AllocId.ofUInt64 value).isSome = true) : Memory.AllocId :=
  checkedSome (Memory.AllocId.ofUInt64 value) success

@[noinline] def checkedCtfe (id : Memory.AllocId) (immutable sharedRef : Bool)
    (success : (Memory.CtfeProvenance.fromParts (id, immutable, sharedRef)).toOption.isSome = true) :
    Memory.CtfeProvenance :=
  checkedSome (Memory.CtfeProvenance.fromParts (id, immutable, sharedRef)).toOption success

instance : ToExpr Memory.AllocId where
  toTypeExpr := mkConst ``Memory.AllocId
  toExpr id := mkApp2 (mkConst ``checkedAllocId) (toExpr id.value) trueRefl

instance : ToExpr Memory.CtfeProvenance where
  toTypeExpr := mkConst ``Memory.CtfeProvenance
  toExpr prov := mkApp4 (mkConst ``checkedCtfe) (toExpr prov.allocId)
    (toExpr prov.immutable) (toExpr prov.sharedRef) trueRefl

deriving instance ToExpr for JsonNumber

private def exprList (type : Expr) (items : List Expr) : Expr :=
  items.foldr (fun value rest => mkApp3 (mkConst ``List.cons [0]) type value rest)
    (mkApp (mkConst ``List.nil [0]) type)

private partial def jsonExpr (value : Json) : Expr :=
  match value with
    | .null => mkConst ``Json.null
    | .bool b => mkApp (mkConst ``Json.bool) (toExpr b)
    | .num n => mkApp (mkConst ``Json.num) (toExpr n)
    | .str s => mkApp (mkConst ``Json.str) (toExpr s)
    | .arr xs =>
      let items := xs.map jsonExpr
      mkApp (mkConst ``Json.arr) (mkApp2 (mkConst ``List.toArray [0]) (mkConst ``Json) (exprList (mkConst ``Json) items.toList))
    | .obj fields =>
      let pairs := fields.toList.map fun (key, value) =>
        mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``Json)
          (toExpr key) (jsonExpr value)
      let list := exprList (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Json)) pairs
      mkApp (mkConst ``Json.mkObj) list

instance : ToExpr Json where
  toTypeExpr := mkConst ``Json
  toExpr := jsonExpr

section
variable [ToExpr Json]

deriving instance ToExpr for MIR.IntegerKind
deriving instance ToExpr for MIR.BinOp
deriving instance ToExpr for MIR.UnOp
deriving instance ToExpr for MIR.Mutability
deriving instance ToExpr for MIR.BoundVarIndexKind
deriving instance ToExpr for MIR.BoundRegionKind
deriving instance ToExpr for MIR.BoundTypeKind
deriving instance ToExpr for MIR.BoundVariableKind
deriving instance ToExpr for MIR.LateParamRegionKind
deriving instance ToExpr for MIR.Region
deriving instance ToExpr for MIR.GenericArg
deriving instance ToExpr for MIR.ConstAliasKind
deriving instance ToExpr for MIR.ConstExpressionCastKind
deriving instance ToExpr for MIR.ConstExpressionKind
deriving instance ToExpr for MIR.ValTreeNode
deriving instance ToExpr for MIR.ValTree
deriving instance ToExpr for MIR.TypeConst
deriving instance ToExpr for Input.TypeShapeKind
deriving instance ToExpr for Input.StatementVariant
deriving instance ToExpr for Input.TerminatorVariant
deriving instance ToExpr for Input.RvalueVariant
deriving instance ToExpr for Input.OperandVariant
deriving instance ToExpr for Input.ProjectionVariant
deriving instance ToExpr for Input.LayoutKind
deriving instance ToExpr for Input.LayoutVariantsKind
deriving instance ToExpr for Input.BackendReprKind
deriving instance ToExpr for Input.FieldShapeKind
deriving instance ToExpr for Input.IntegerTypeTag
deriving instance ToExpr for Input.FloatTypeTag
deriving instance ToExpr for Input.AdtKind
deriving instance ToExpr for Input.TypeShapeMetadata
deriving instance ToExpr for Input.PrimitiveKind
deriving instance ToExpr for Input.ScalarShapeKind
deriving instance ToExpr for Input.PassModeKind
deriving instance ToExpr for Input.AllocationKind
deriving instance ToExpr for Input.InstanceKind
deriving instance ToExpr for Input.Obligation
deriving instance ToExpr for Input.SourcePosition
deriving instance ToExpr for Input.SourceSpanData
deriving instance ToExpr for Input.SourceInfo
deriving instance ToExpr for Input.Producer
deriving instance ToExpr for Input.TaggedNode
deriving instance ToExpr for Input.FieldShape
deriving instance ToExpr for Input.PrimitiveLayout
deriving instance ToExpr for Input.ScalarLayout
deriving instance ToExpr for Input.NicheLayout
deriving instance ToExpr for Input.BackendRepr
deriving instance ToExpr for Input.LayoutVariant
deriving instance ToExpr for Input.TagEncodingKind
deriving instance ToExpr for Input.TagEncoding
deriving instance ToExpr for Input.VariantsLayout
deriving instance ToExpr for Input.Layout
deriving instance ToExpr for Input.ExternAbi
deriving instance ToExpr for Input.ArmCallKind
deriving instance ToExpr for Input.InterruptCallKind
deriving instance ToExpr for Input.X86CallKind
deriving instance ToExpr for Input.CanonicalAbiKind
deriving instance ToExpr for Input.CanonicalAbi
deriving instance ToExpr for Input.TypedEnumTag
deriving instance ToExpr for Input.UserTypeProjectionKind
deriving instance ToExpr for Input.UserTypeProjection
deriving instance ToExpr for Input.FunctionSignature
deriving instance ToExpr for Input.CompilerPattern
deriving instance ToExpr for Input.AdtCompilerFacts
deriving instance ToExpr for Input.ProjectionField
deriving instance ToExpr for Input.ProjectionParent
deriving instance ToExpr for Input.ProjectionQueries
deriving instance ToExpr for Input.DiscriminantValue
deriving instance ToExpr for Input.DiscriminantInfo
deriving instance ToExpr for Input.TypeCompilerFacts
deriving instance ToExpr for Input.ReprInteger
deriving instance ToExpr for Input.ScalableElement
deriving instance ToExpr for Input.ReprOptions
deriving instance ToExpr for Input.AdtField
deriving instance ToExpr for Input.AdtVariant
deriving instance ToExpr for Input.AdtShape
deriving instance ToExpr for Input.ArrayConstructor
deriving instance ToExpr for Input.AliasTypeKind
deriving instance ToExpr for Input.TypeShape
deriving instance ToExpr for Input.TypeNode
deriving instance ToExpr for Input.InitRange
deriving instance ToExpr for Input.Relocation
deriving instance ToExpr for Input.MemoryMutability
deriving instance ToExpr for Input.AllocationMemory
deriving instance ToExpr for Input.ArgumentExtensionKind
deriving instance ToExpr for Input.ArgumentCaptureKind
deriving instance ToExpr for Input.IndirectModeKind
deriving instance ToExpr for Input.AbiAttributes
deriving instance ToExpr for Input.AbiRegisterKind
deriving instance ToExpr for Input.AbiRegisterHint
deriving instance ToExpr for Input.AbiRegister
deriving instance ToExpr for Input.AbiCastTarget
deriving instance ToExpr for Input.AbiPassMode
deriving instance ToExpr for Input.AbiArgument
deriving instance ToExpr for Input.FunctionAbi
deriving instance ToExpr for Input.TypedValue

section
variable [ToExpr Input.TypedValue]
deriving instance ToExpr for Input.DefinitionId
deriving instance ToExpr for Input.VtableEntryKind
deriving instance ToExpr for Input.VtablePredicateKind
deriving instance ToExpr for Input.FunctionAllocation
deriving instance ToExpr for Input.StaticGlobalInfo
deriving instance ToExpr for Input.StaticAllocation
deriving instance ToExpr for Input.VtablePredicate
deriving instance ToExpr for Input.VtableEntry
deriving instance ToExpr for Input.VtableAllocation
deriving instance ToExpr for Input.AllocationData
deriving instance ToExpr for Input.AllocationNode
deriving instance ToExpr for Input.MirNode
deriving instance ToExpr for Input.CallResolutionKind
deriving instance ToExpr for Input.CallResolutionEvidence
deriving instance ToExpr for Input.InlinedScope
deriving instance ToExpr for Input.SourceScope
deriving instance ToExpr for Input.CompilerSourcePosition
deriving instance ToExpr for Input.BacktraceSpan
deriving instance ToExpr for Input.BasicBlock
deriving instance ToExpr for Input.LocalDecl
deriving instance ToExpr for Input.BodyInputPhase
deriving instance ToExpr for Input.RequiredConstantCheck
deriving instance ToExpr for Input.ConstantQueryContext
deriving instance ToExpr for Input.BodyCore
deriving instance ToExpr for Input.PromotedBody
deriving instance ToExpr for Input.Body
deriving instance ToExpr for Input.BodyRoot
deriving instance ToExpr for Interpreter.CallReifyReason
deriving instance ToExpr for Interpreter.CallShimKind
deriving instance ToExpr for Interpreter.CallInstanceKind
deriving instance ToExpr for Input.InstanceNode
deriving instance ToExpr for Input.ScopeRoot
deriving instance ToExpr for Input.SelectedScope
deriving instance ToExpr for Input.TargetDataLayoutEvidence
deriving instance ToExpr for Input.CompilerPredicateEvidence
deriving instance ToExpr for Input.SourceAllocIdKind
deriving instance ToExpr for Input.SourceAllocIdStatus
deriving instance ToExpr for Input.SourceAllocIdPoolRow
deriving instance ToExpr for Input.SourceAllocIdDedupKind
deriving instance ToExpr for Input.SourceAllocIdProbeOutcome
deriving instance ToExpr for Input.SourceAllocIdSaltResult
deriving instance ToExpr for Input.SourceAllocIdDedupRow
deriving instance ToExpr for Input.CompilerAllocIdWorld
deriving instance ToExpr for Input.ImportDocument
deriving instance ToExpr for Input.ExecutionInput

end
end

private def addAuxDefinition (name : Name) (type value : Expr) : MetaM Unit := do
  let declaration := Declaration.defnDecl {
    name := name
    levelParams := []
    type := type
    value := value
    hints := .regular 0
    safety := .safe
  }
  addDecl declaration
  -- Preserve the references during code generation as well as in kernel terms.
  Meta.setInlineAttribute name .noinline
  compileDecl declaration

/-- Keep large imports within the compiler's recursion limits by naming
closed constructor subtrees. Every auxiliary declaration is kernel checked. -/
private structure SplitState where
  next : Nat := 0

private partial def splitValue (base : Name) (value : Expr) :
    StateT SplitState MetaM (Expr × Nat) := do
  let (value, size) ← match value with
    | .app fn arg => do
      let (fn, fnSize) ← splitValue base fn
      let (arg, argSize) ← splitValue base arg
      pure (mkApp fn arg, fnSize + argSize + 1)
    | _ => pure (value, 1)
  if size < 1024 then
    return (value,size)
  let type ← Meta.inferType value
  if type.isForall || (← Meta.isProp type) then
    return (value,size)
  let index := (← get).next
  modify fun state => { state with next := index + 1 }
  let name := base ++ Name.mkSimple s!"_mir_chunk_{index}"
  addAuxDefinition name type value
  let result := (mkConst name, 1)
  return result

private def exprArray (type : Expr) (items : Array Expr) : Expr :=
  mkApp2 (mkConst ``List.toArray [0]) type (exprList type items.toList)

private abbrev QuoteM := Id

mutual
private partial def typedValueExpr [ToExpr Json] (value : Input.TypedValue) : QuoteM Expr := do
  let expr ← match value with
    | .scalar value => do
      pure <| mkApp (mkConst ``Input.TypedValue.scalar) (toExpr value)
    | .diagnostic value => do
      pure <| mkApp (mkConst ``Input.TypedValue.diagnostic) (toExpr value)
    | .array values => do
      let children ← values.mapM typedValueExpr
      pure <| mkApp (mkConst ``Input.TypedValue.array) (exprArray (mkConst ``Input.TypedValue) children)
    | .object fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp (mkConst ``Input.TypedValue.object) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
    | .typeRef id => do
      pure <| mkApp (mkConst ``Input.TypedValue.typeRef) (toExpr id)
    | .allocationRef id => do
      pure <| mkApp (mkConst ``Input.TypedValue.allocationRef) (toExpr id)
    | .instanceRef id => do
      pure <| mkApp (mkConst ``Input.TypedValue.instanceRef) (toExpr id)
    | .localRef id => do
      pure <| mkApp (mkConst ``Input.TypedValue.localRef) (toExpr id)
    | .blockRef id => do
      pure <| mkApp (mkConst ``Input.TypedValue.blockRef) (toExpr id)
    | .sourceSpan value => do
      pure <| mkApp (mkConst ``Input.TypedValue.sourceSpan) (toExpr value)
    | .sourceInfo value => do
      pure <| mkApp (mkConst ``Input.TypedValue.sourceInfo) (toExpr value)
    | .statement variant fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp2 (mkConst ``Input.TypedValue.statement) (toExpr variant) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
    | .terminator variant fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp2 (mkConst ``Input.TypedValue.terminator) (toExpr variant) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
    | .rvalue variant fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp2 (mkConst ``Input.TypedValue.rvalue) (toExpr variant) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
    | .binOperator operator => do
      pure <| mkApp (mkConst ``Input.TypedValue.binOperator) (toExpr operator)
    | .unOperator operator => do
      pure <| mkApp (mkConst ``Input.TypedValue.unOperator) (toExpr operator)
    | .enumTag category tag fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp3 (mkConst ``Input.TypedValue.enumTag) (toExpr category) (toExpr tag) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
    | .userTypeProjection value => do
      pure <| mkApp (mkConst ``Input.TypedValue.userTypeProjection) (toExpr value)
    | .operand variant fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp2 (mkConst ``Input.TypedValue.operand) (toExpr variant) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
    | .projection variant fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp2 (mkConst ``Input.TypedValue.projection) (toExpr variant) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
  pure expr
end

/-- Import an accepted document as a closed, kernel-checked Lean value.
Malformed or failed compiler input is rejected before declarations are created.
This command never produces a safety theorem. -/
syntax (name := importMir) "import_mir " str " as " ident : command

open Elab Command in
elab_rules : command
  | `(import_mir $path:str as $name:ident) => do
    let decoded ← liftIO <| Input.decodeFile path.getString
    let result ← match decoded with
      | .ok result => pure result
      | .error message => throwErrorAt path "MIR import failed: {message}"
    let declName := (← getCurrNamespace) ++ name.getId
    -- Thousands of auxiliary definitions must not each retain an asynchronous
    -- environment snapshot until the end of this single command.
    let (value, _) ← liftTermElabM <| withOptions (Elab.async.set · false) do
      letI : ToExpr Json := { toTypeExpr := mkConst ``Json, toExpr := jsonExpr }
      letI : ToExpr Input.TypedValue := {
        toTypeExpr := mkConst ``Input.TypedValue
        toExpr := fun value => (typedValueExpr value).run
      }
      (splitValue declName (toExpr result)).run' {}
    liftCoreM <| withOptions (Elab.async.set · false) <| addAndCompile <| .defnDecl {
      name := declName
      levelParams := []
      type := mkConst ``Input.ExecutionInput
      value := value
      hints := .regular 0
      safety := .safe
    }

end Miri.Frontend
