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

deriving instance ToExpr for Except
deriving instance ToExpr for JsonNumber

private def exprList (type : Expr) (items : List Expr) : Expr :=
  items.foldr (fun value rest => mkApp3 (mkConst ``List.cons [0]) type value rest)
    (mkApp (mkConst ``List.nil [0]) type)

private partial def jsonExpr (shared : Std.HashMap Json Expr) (value : Json) : Expr :=
  match (if shared.isEmpty then none else shared[value]?) with
  | some expr => expr
  | none => match value with
    | .null => mkConst ``Json.null
    | .bool b => mkApp (mkConst ``Json.bool) (toExpr b)
    | .num n => mkApp (mkConst ``Json.num) (toExpr n)
    | .str s => mkApp (mkConst ``Json.str) (toExpr s)
    | .arr xs =>
      let items := xs.map (jsonExpr shared)
      mkApp (mkConst ``Json.arr) (mkApp2 (mkConst ``List.toArray [0]) (mkConst ``Json) (exprList (mkConst ``Json) items.toList))
    | .obj fields =>
      let pairs := fields.toList.map fun (key, value) =>
        mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String) (mkConst ``Json)
          (toExpr key) (jsonExpr shared value)
      let list := exprList (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Json)) pairs
      mkApp (mkConst ``Json.mkObj) list

instance : ToExpr Json where
  toTypeExpr := mkConst ``Json
  toExpr := jsonExpr {}

open Lean Elab Command in
private partial def deriveQuote (name : Name) : StateT NameSet CommandElabM Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  let some info := (← getEnv).find? name | return
  if !name.toString.startsWith "Miri." then return
  match info with
  | .inductInfo indInfo =>
    let existing ← liftM <| liftTermElabM <| Meta.forallTelescopeReducing indInfo.type fun xs _ => do
      Meta.synthInstance? (← Meta.mkAppM ``ToExpr
        #[mkAppN (mkConst name (indInfo.levelParams.map Level.param)) xs])
    if existing.isSome then return
    for ctor in indInfo.ctors do
      for dependency in (← getConstInfo ctor).type.getUsedConstants do
        if dependency != name then deriveQuote dependency
    liftM <| elabCommand (← `(deriving instance ToExpr for $(mkIdent name)))
  | .defnInfo definition =>
    let typeFormer ← liftM <| liftTermElabM <|
      Meta.forallTelescopeReducing definition.type fun _ body => pure body.isSort
    if typeFormer then
      for dependency in definition.value.getUsedConstants do
        if dependency != name then deriveQuote dependency
  | _ => pure ()

section
-- Propagate the import-local JSON quotation table through all derived quoters.
variable [ToExpr Json]

run_cmd discard <| (deriveQuote ``MIR.IntegerKind).run {}
run_cmd discard <| (deriveQuote ``MIR.BinOp).run {}
run_cmd discard <| (deriveQuote ``MIR.UnOp).run {}
run_cmd discard <| (deriveQuote ``Input.PayloadStatus).run {}
run_cmd discard <| (deriveQuote ``Input.TypeShapeKind).run {}
run_cmd discard <| (deriveQuote ``Input.StatementVariant).run {}
run_cmd discard <| (deriveQuote ``Input.TerminatorVariant).run {}
run_cmd discard <| (deriveQuote ``Input.RvalueVariant).run {}
run_cmd discard <| (deriveQuote ``Input.OperandVariant).run {}
run_cmd discard <| (deriveQuote ``Input.ProjectionVariant).run {}
run_cmd discard <| (deriveQuote ``Input.LayoutKind).run {}
run_cmd discard <| (deriveQuote ``Input.LayoutVariantsKind).run {}
run_cmd discard <| (deriveQuote ``Input.BackendReprKind).run {}
run_cmd discard <| (deriveQuote ``Input.FieldShapeKind).run {}
run_cmd discard <| (deriveQuote ``Input.IntegerTypeTag).run {}
run_cmd discard <| (deriveQuote ``Input.FloatTypeTag).run {}
run_cmd discard <| (deriveQuote ``Input.AdtKind).run {}
run_cmd discard <| (deriveQuote ``Input.TypeShapeMetadata).run {}
run_cmd discard <| (deriveQuote ``Input.PrimitiveKind).run {}
run_cmd discard <| (deriveQuote ``Input.ScalarShapeKind).run {}
run_cmd discard <| (deriveQuote ``Input.PassModeKind).run {}
run_cmd discard <| (deriveQuote ``Input.AllocationKind).run {}
run_cmd discard <| (deriveQuote ``Input.InstanceKind).run {}
run_cmd discard <| (deriveQuote ``Input.Obligation).run {}
run_cmd discard <| (deriveQuote ``Input.SourcePosition).run {}
run_cmd discard <| (deriveQuote ``Input.SourceSpanData).run {}
run_cmd discard <| (deriveQuote ``Input.SourceInfo).run {}
run_cmd discard <| (deriveQuote ``Input.Producer).run {}
run_cmd discard <| (deriveQuote ``Input.TaggedNode).run {}
run_cmd discard <| (deriveQuote ``Input.FieldShape).run {}
run_cmd discard <| (deriveQuote ``Input.PrimitiveLayout).run {}
run_cmd discard <| (deriveQuote ``Input.ScalarLayout).run {}
run_cmd discard <| (deriveQuote ``Input.BackendRepr).run {}
run_cmd discard <| (deriveQuote ``Input.NicheLayout).run {}
run_cmd discard <| (deriveQuote ``Input.LayoutVariant).run {}
run_cmd discard <| (deriveQuote ``Input.TagEncodingKind).run {}
run_cmd discard <| (deriveQuote ``Input.TagEncoding).run {}
run_cmd discard <| (deriveQuote ``Input.VariantsLayout).run {}
run_cmd discard <| (deriveQuote ``Input.Layout).run {}
run_cmd discard <| (deriveQuote ``Input.ArmCallKind).run {}
run_cmd discard <| (deriveQuote ``Input.InterruptCallKind).run {}
run_cmd discard <| (deriveQuote ``Input.X86CallKind).run {}
run_cmd discard <| (deriveQuote ``Input.CanonicalAbiKind).run {}
run_cmd discard <| (deriveQuote ``Input.CanonicalAbi).run {}
run_cmd discard <| (deriveQuote ``Input.TypedEnumTag).run {}
run_cmd discard <| (deriveQuote ``Input.UserTypeProjectionKind).run {}
run_cmd discard <| (deriveQuote ``Input.UserTypeProjection).run {}
run_cmd discard <| (deriveQuote ``Input.CompilerBooleanEvidence).run {}
run_cmd discard <| (deriveQuote ``Input.CompilerTypeEvidence).run {}
run_cmd discard <| (deriveQuote ``Input.ProjectionField).run {}
run_cmd discard <| (deriveQuote ``Input.ProjectionParent).run {}
run_cmd discard <| (deriveQuote ``Input.ProjectionValue).run {}
run_cmd discard <| (deriveQuote ``Input.ProjectionEvidence).run {}
run_cmd discard <| (deriveQuote ``Input.ProjectionTables).run {}
run_cmd discard <| (deriveQuote ``Input.DefinitionId).run {}
run_cmd discard <| (deriveQuote ``Input.CompilerAdtFacts).run {}
run_cmd discard <| (deriveQuote ``Input.CompilerDiscriminantValue).run {}
run_cmd discard <| (deriveQuote ``Input.CompilerDiscriminants).run {}
run_cmd discard <| (deriveQuote ``Input.CompilerFactTables).run {}
run_cmd discard <| (deriveQuote ``Input.TypeCompilerFacts).run {}
run_cmd discard <| (deriveQuote ``Input.TypeField).run {}
run_cmd discard <| (deriveQuote ``Input.TypeVariant).run {}
run_cmd discard <| (deriveQuote ``Input.RepresentationInteger).run {}
run_cmd discard <| (deriveQuote ``Input.ScalableRepresentation).run {}
run_cmd discard <| (deriveQuote ``Input.TypeRepresentation).run {}
run_cmd discard <| (deriveQuote ``Input.ArrayConstructorEvidence).run {}
run_cmd discard <| (deriveQuote ``Input.PredicateListData).run {}
run_cmd discard <| (deriveQuote ``Input.TypeRelations).run {}
run_cmd discard <| (deriveQuote ``Input.TypeRelationTables).run {}
run_cmd discard <| (deriveQuote ``Input.TypeNode).run {}
run_cmd discard <| (deriveQuote ``Input.InitRange).run {}
run_cmd discard <| (deriveQuote ``Input.Relocation).run {}
run_cmd discard <| (deriveQuote ``Input.MemoryMutability).run {}
run_cmd discard <| (deriveQuote ``Input.AllocationMemory).run {}
run_cmd discard <| (deriveQuote ``Input.AbiTag).run {}
run_cmd discard <| (deriveQuote ``Input.AbiAttributes).run {}
run_cmd discard <| (deriveQuote ``Input.AbiRegisterKind).run {}
run_cmd discard <| (deriveQuote ``Input.AbiHintKind).run {}
run_cmd discard <| (deriveQuote ``Input.AbiHintElement).run {}
run_cmd discard <| (deriveQuote ``Input.AbiRegister).run {}
run_cmd discard <| (deriveQuote ``Input.AbiCastTarget).run {}
run_cmd discard <| (deriveQuote ``Input.AbiPassMode).run {}
run_cmd discard <| (deriveQuote ``Input.AbiArgument).run {}
run_cmd discard <| (deriveQuote ``Input.FunctionAbi).run {}
run_cmd discard <| (deriveQuote ``Input.AbiArgumentData).run {}
run_cmd discard <| (deriveQuote ``Input.FunctionAbiData).run {}
run_cmd discard <| (deriveQuote ``Input.AbiTables).run {}
run_cmd discard <| (deriveQuote ``Input.TypedValue).run {}

section
variable [ToExpr Input.TypedValue]
run_cmd discard <| (deriveQuote ``Input.VtableEntryKind).run {}
run_cmd discard <| (deriveQuote ``Input.VtablePredicateKind).run {}
run_cmd discard <| (deriveQuote ``Input.FunctionAllocation).run {}
run_cmd discard <| (deriveQuote ``Input.StaticGlobalInfo).run {}
run_cmd discard <| (deriveQuote ``Input.StaticAllocation).run {}
run_cmd discard <| (deriveQuote ``Input.VtablePredicate).run {}
run_cmd discard <| (deriveQuote ``Input.VtableEntry).run {}
run_cmd discard <| (deriveQuote ``Input.VtableEntryData).run {}
run_cmd discard <| (deriveQuote ``Input.VtableMetadataData).run {}
run_cmd discard <| (deriveQuote ``Input.VtableQueryData).run {}
run_cmd discard <| (deriveQuote ``Input.VtableTables).run {}
run_cmd discard <| (deriveQuote ``Input.VtableAllocation).run {}
run_cmd discard <| (deriveQuote ``Input.AllocationData).run {}
run_cmd discard <| (deriveQuote ``Input.AllocationNode).run {}
run_cmd discard <| (deriveQuote ``Input.MirNode).run {}
run_cmd discard <| (deriveQuote ``Input.BasicBlock).run {}
run_cmd discard <| (deriveQuote ``Input.LocalDecl).run {}
run_cmd discard <| (deriveQuote ``Input.BodyCore).run {}
run_cmd discard <| (deriveQuote ``Input.PromotedBody).run {}
run_cmd discard <| (deriveQuote ``Input.Body).run {}
run_cmd discard <| (deriveQuote ``Input.InstanceNode).run {}
run_cmd discard <| (deriveQuote ``Input.ScopeRoot).run {}
run_cmd discard <| (deriveQuote ``Input.SelectedScope).run {}
run_cmd discard <| (deriveQuote ``Input.TargetDataLayoutEvidence).run {}
run_cmd discard <| (deriveQuote ``Input.CompilerPredicateEvidence).run {}
run_cmd discard <| (deriveQuote ``Input.SourceAllocIdKind).run {}
run_cmd discard <| (deriveQuote ``Input.SourceAllocIdStatus).run {}
run_cmd discard <| (deriveQuote ``Input.SourceAllocIdPoolRow).run {}
run_cmd discard <| (deriveQuote ``Input.SourceAllocIdDedupKind).run {}
run_cmd discard <| (deriveQuote ``Input.SourceAllocIdProbeOutcome).run {}
run_cmd discard <| (deriveQuote ``Input.SourceAllocIdSaltResult).run {}
run_cmd discard <| (deriveQuote ``Input.SourceAllocIdDedupRow).run {}
run_cmd discard <| (deriveQuote ``Input.CompilerAllocIdWorld).run {}
run_cmd discard <| (deriveQuote ``MIR.Location).run {}
run_cmd discard <| (deriveQuote ``MIR.SpanRef).run {}
run_cmd discard <| (deriveQuote ``MIR.Mutability).run {}
run_cmd discard <| (deriveQuote ``MIR.Safety).run {}
run_cmd discard <| (deriveQuote ``MIR.Variance).run {}
run_cmd discard <| (deriveQuote ``MIR.PointerCoercion).run {}
run_cmd discard <| (deriveQuote ``MIR.CoercionSource).run {}
run_cmd discard <| (deriveQuote ``MIR.CastKind).run {}
run_cmd discard <| (deriveQuote ``MIR.FakeBorrowKind).run {}
run_cmd discard <| (deriveQuote ``MIR.MutBorrowKind).run {}
run_cmd discard <| (deriveQuote ``MIR.BorrowKind).run {}
run_cmd discard <| (deriveQuote ``MIR.RawPtrKind).run {}
run_cmd discard <| (deriveQuote ``MIR.WithRetag).run {}
run_cmd discard <| (deriveQuote ``MIR.RuntimeChecks).run {}
run_cmd discard <| (deriveQuote ``MIR.LoopHintAttr).run {}
run_cmd discard <| (deriveQuote ``MIR.FakeReadCause).run {}
run_cmd discard <| (deriveQuote ``MIR.CallSource).run {}
run_cmd discard <| (deriveQuote ``MIR.InlineAsmMacro).run {}
run_cmd discard <| (deriveQuote ``MIR.UnwindTerminateReason).run {}
run_cmd discard <| (deriveQuote ``MIR.UnwindAction).run {}
run_cmd discard <| (deriveQuote ``MIR.CoroutineSource).run {}
run_cmd discard <| (deriveQuote ``MIR.CoroutineDesugaring).run {}
run_cmd discard <| (deriveQuote ``MIR.Movability).run {}
run_cmd discard <| (deriveQuote ``MIR.CoroutineKind).run {}
run_cmd discard <| (deriveQuote ``MIR.HirId).run {}
run_cmd discard <| (deriveQuote ``MIR.CoveragePointKind).run {}
run_cmd discard <| (deriveQuote ``MIR.CoverageKind).run {}
run_cmd discard <| (deriveQuote ``MIR.BackwardIncompatibleDropReason).run {}
run_cmd discard <| (deriveQuote ``MIR.ProjectionKind).run {}
run_cmd discard <| (deriveQuote ``MIR.UserTypeProjection).run {}
run_cmd discard <| (deriveQuote ``MIR.AnalysisPhase).run {}
run_cmd discard <| (deriveQuote ``MIR.RuntimePhase).run {}
run_cmd discard <| (deriveQuote ``MIR.MirPhase).run {}
run_cmd discard <| (deriveQuote ``MIR.ConstPointer).run {}
run_cmd discard <| (deriveQuote ``MIR.ScalarValue).run {}
run_cmd discard <| (deriveQuote ``MIR.ConstValue).run {}
run_cmd discard <| (deriveQuote ``MIR.ConstAliasKind).run {}
run_cmd discard <| (deriveQuote ``MIR.ConstExpressionCastKind).run {}
run_cmd discard <| (deriveQuote ``MIR.ConstExpressionKind).run {}
run_cmd discard <| (deriveQuote ``MIR.BoundVarIndexKind).run {}
run_cmd discard <| (deriveQuote ``MIR.BoundRegionKind).run {}
run_cmd discard <| (deriveQuote ``MIR.BoundTypeKind).run {}
run_cmd discard <| (deriveQuote ``MIR.BoundVariableKind).run {}
run_cmd discard <| (deriveQuote ``MIR.LateParamRegionKind).run {}
run_cmd discard <| (deriveQuote ``MIR.Region).run {}
run_cmd discard <| (deriveQuote ``MIR.GenericArg).run {}
run_cmd discard <| (deriveQuote ``MIR.ValTreeNode).run {}
run_cmd discard <| (deriveQuote ``MIR.ValTree).run {}
run_cmd discard <| (deriveQuote ``MIR.TypeConst).run {}
run_cmd discard <| (deriveQuote ``MIR.UnevaluatedConst).run {}
run_cmd discard <| (deriveQuote ``MIR.MirConst).run {}
run_cmd discard <| (deriveQuote ``MIR.ConstOperand).run {}
run_cmd discard <| (deriveQuote ``MIR.ProjectionElem).run {}
run_cmd discard <| (deriveQuote ``MIR.Place).run {}
run_cmd discard <| (deriveQuote ``MIR.Operand).run {}
run_cmd discard <| (deriveQuote ``MIR.CopyNonOverlappingForm).run {}
run_cmd discard <| (deriveQuote ``MIR.NonDivergingIntrinsicForm).run {}
run_cmd discard <| (deriveQuote ``MIR.AggregateForm).run {}
run_cmd discard <| (deriveQuote ``MIR.RvalueForm).run {}
run_cmd discard <| (deriveQuote ``MIR.StatementKindForm).run {}
run_cmd discard <| (deriveQuote ``MIR.SwitchTarget).run {}
run_cmd discard <| (deriveQuote ``MIR.SwitchTargets).run {}
run_cmd discard <| (deriveQuote ``MIR.SpannedOperandForm).run {}
run_cmd discard <| (deriveQuote ``MIR.InlineAsmOptions).run {}
run_cmd discard <| (deriveQuote ``MIR.InlineAsmTemplatePiece).run {}
run_cmd discard <| (deriveQuote ``MIR.InlineAsmArch).run {}
run_cmd discard <| (deriveQuote ``MIR.InlineAsmRegOrRegClass).run {}
run_cmd discard <| (deriveQuote ``MIR.InlineAsmOperandForm).run {}
run_cmd discard <| (deriveQuote ``MIR.InlineAsmTerminatorForm).run {}
run_cmd discard <| (deriveQuote ``MIR.AssertKindForm).run {}
run_cmd discard <| (deriveQuote ``MIR.TerminatorKindForm).run {}
run_cmd discard <| (deriveQuote ``MIR.SourceInfo).run {}
run_cmd discard <| (deriveQuote ``MIR.Statement).run {}
run_cmd discard <| (deriveQuote ``MIR.Terminator).run {}
run_cmd discard <| (deriveQuote ``MIR.BasicBlock).run {}
run_cmd discard <| (deriveQuote ``MIR.Body).run {}
run_cmd discard <| (deriveQuote ``MIR.PlaceId).run {}
run_cmd discard <| (deriveQuote ``MIR.ProjectionId).run {}
run_cmd discard <| (deriveQuote ``MIR.ProjectionListId).run {}
run_cmd discard <| (deriveQuote ``MIR.OperandId).run {}
run_cmd discard <| (deriveQuote ``MIR.OperandListId).run {}
run_cmd discard <| (deriveQuote ``MIR.ConstantId).run {}
run_cmd discard <| (deriveQuote ``MIR.RvalueId).run {}
run_cmd discard <| (deriveQuote ``MIR.StatementId).run {}
run_cmd discard <| (deriveQuote ``MIR.TerminatorId).run {}
run_cmd discard <| (deriveQuote ``MIR.BlockNodeId).run {}
run_cmd discard <| (deriveQuote ``MIR.BodyId).run {}
run_cmd discard <| (deriveQuote ``MIR.ConstantNode).run {}
run_cmd discard <| (deriveQuote ``MIR.PlaceNode).run {}
run_cmd discard <| (deriveQuote ``MIR.OperandNode).run {}
run_cmd discard <| (deriveQuote ``MIR.StatementNode).run {}
run_cmd discard <| (deriveQuote ``MIR.TerminatorNode).run {}
run_cmd discard <| (deriveQuote ``MIR.BlockNode).run {}
run_cmd discard <| (deriveQuote ``MIR.BodyNode).run {}
run_cmd discard <| (deriveQuote ``MIR.SyntaxTables).run {}
run_cmd discard <| (deriveQuote ``Miri.Interpreter.CallReifyReason).run {}
run_cmd discard <| (deriveQuote ``Miri.Interpreter.CallShimKind).run {}
run_cmd discard <| (deriveQuote ``Miri.Interpreter.CallInstanceKind).run {}
run_cmd discard <| (deriveQuote ``Miri.Interpreter.CallInstance).run {}
run_cmd discard <| (deriveQuote ``Miri.Interpreter.CallFunctionKind).run {}
run_cmd discard <| (deriveQuote ``Miri.ABI.ExternAbi).run {}
run_cmd discard <| (deriveQuote ``Input.FunctionTypeData).run {}
run_cmd discard <| (deriveQuote ``Input.FunctionQueryData).run {}
run_cmd discard <| (deriveQuote ``Miri.ABI.ArmCall).run {}
run_cmd discard <| (deriveQuote ``Miri.ABI.InterruptKind).run {}
run_cmd discard <| (deriveQuote ``Miri.ABI.X86Call).run {}
run_cmd discard <| (deriveQuote ``Miri.ABI.CanonAbi).run {}
run_cmd discard <| (deriveQuote ``Miri.Interpreter.ForeignItems.SignatureType).run {}
run_cmd discard <| (deriveQuote ``Miri.Interpreter.ForeignItems.Signature).run {}
run_cmd discard <| (deriveQuote ``Input.InstanceAbiQuery).run {}
run_cmd discard <| (deriveQuote ``Input.ShimAbiQuery).run {}
run_cmd discard <| (deriveQuote ``Input.NamedShimAbiQuery).run {}
run_cmd discard <| (deriveQuote ``Input.PointerAbiQuery).run {}
run_cmd discard <| (deriveQuote ``Input.SignatureAbiQuery).run {}
run_cmd discard <| (deriveQuote ``Input.CovarianceQuery).run {}
run_cmd discard <| (deriveQuote ``Input.AbiQueries).run {}
run_cmd discard <| (deriveQuote ``Input.IntrinsicData).run {}
run_cmd discard <| (deriveQuote ``Input.RuntimeTypeData).run {}
run_cmd discard <| (deriveQuote ``Input.RuntimeVirtualData).run {}
run_cmd discard <| (deriveQuote ``Input.NativeSignatureData).run {}
run_cmd discard <| (deriveQuote ``Input.RuntimeInstanceData).run {}
run_cmd discard <| (deriveQuote ``Input.CompilerTables).run {}
run_cmd discard <| (deriveQuote ``Input.SourceScopeData).run {}
run_cmd discard <| (deriveQuote ``Input.BodySourceData).run {}
run_cmd discard <| (deriveQuote ``Input.PatternData).run {}
run_cmd discard <| (deriveQuote ``Input.NormalizationData).run {}
run_cmd discard <| (deriveQuote ``Input.MIRInputTables).run {}
run_cmd discard <| (deriveQuote ``Input.ImportDocument).run {}
run_cmd discard <| (deriveQuote ``Input.ExecutionInput).run {}
run_cmd discard <| (deriveQuote ``Input.DecodeResult).run {}

end
end

private def addSharedDefinition (name : Name) (type value : Expr) : MetaM Unit := do
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
  cache : Std.HashMap Expr (Expr × Nat) := {}

private partial def splitValue (base : Name) (value : Expr) :
    StateT SplitState MetaM (Expr × Nat) := do
  if let some cached := (← get).cache[value]? then return cached
  let original := value
  let (value, size) ← match value with
    | .app fn arg => do
      let (fn, fnSize) ← splitValue base fn
      let (arg, argSize) ← splitValue base arg
      pure (mkApp fn arg, fnSize + argSize + 1)
    | _ => pure (value, 1)
  if size < 1024 then
    modify fun state => { state with cache := state.cache.insert original (value,size) }
    return (value,size)
  let type ← Meta.inferType value
  if type.isForall || (← Meta.isProp type) then
    modify fun state => { state with cache := state.cache.insert original (value,size) }
    return (value,size)
  let index := (← get).next
  modify fun state => { state with next := index + 1 }
  let name := base ++ Name.mkSimple s!"_mir_chunk_{index}"
  addSharedDefinition name type value
  let result := (mkConst name, 1)
  modify fun state => { state with cache := state.cache.insert original result }
  return result

-- Intern constructor expressions while quoting the diagnostic projection too.
-- Its recursive arrays/objects are TypedValue rather than Json, so the JSON
-- table alone cannot prevent their repeated quotation.
private def exprArray (type : Expr) (items : Array Expr) : Expr :=
  mkApp2 (mkConst ``List.toArray [0]) type (exprList type items.toList)

private abbrev QuoteM := StateM (Std.HashMap Expr Expr)

private def internExpr (value : Expr) : QuoteM Expr := do
  if let some previous := (← get)[value]? then return previous
  modify (·.insert value value)
  return value

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
    | .statement variant status fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp3 (mkConst ``Input.TypedValue.statement) (toExpr variant) (toExpr status) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
    | .terminator variant status fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp3 (mkConst ``Input.TypedValue.terminator) (toExpr variant) (toExpr status) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
    | .rvalue variant status fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp3 (mkConst ``Input.TypedValue.rvalue) (toExpr variant) (toExpr status) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
    | .binOperator operator status => do
      pure <| mkApp2 (mkConst ``Input.TypedValue.binOperator) (toExpr operator) (toExpr status)
    | .unknownBinOperator tag status => do
      pure <| mkApp2 (mkConst ``Input.TypedValue.unknownBinOperator) (toExpr tag) (toExpr status)
    | .unOperator operator status => do
      pure <| mkApp2 (mkConst ``Input.TypedValue.unOperator) (toExpr operator) (toExpr status)
    | .unknownUnOperator tag status => do
      pure <| mkApp2 (mkConst ``Input.TypedValue.unknownUnOperator) (toExpr tag) (toExpr status)
    | .enumTag category tag fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp3 (mkConst ``Input.TypedValue.enumTag) (toExpr category) (toExpr tag) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
    | .userTypeProjection value => do
      pure <| mkApp (mkConst ``Input.TypedValue.userTypeProjection) (toExpr value)
    | .operand variant status fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp3 (mkConst ``Input.TypedValue.operand) (toExpr variant) (toExpr status) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
    | .projection variant fields => do
      let children ← fields.mapM fun (key, child) => do
        let child ← typedValueExpr child
        pure <| mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``String)
          (mkConst ``Input.TypedValue) (toExpr key) child
      pure <| mkApp2 (mkConst ``Input.TypedValue.projection) (toExpr variant) (exprArray (mkApp2 (mkConst ``Prod [0, 0]) (mkConst ``String) (mkConst ``Input.TypedValue)) children)
  internExpr expr
end

/-- Quote the resolved catalog in dependency order. Every entry is an ordinary
safe definition, so parents and all typed/raw projections can refer to the same
JSON value without expanding its constructor tree again. The exact JSON key
comparison also permits reuse by reconstructed, structurally equal projections.
The table is local to one import; no unchecked values or global quotation state
are introduced. -/
private def quoteSharedJson (base : Name) (nodes : Array Json) :
    MetaM (Std.HashMap Json Expr) := do
  let mut shared : Std.HashMap Json Expr := {}
  for h : index in [:nodes.size] do
    let node := nodes[index]
    if shared.contains node then continue
    let value := jsonExpr shared node
    let (value, _) ← (splitValue (base ++ Name.mkSimple s!"_mir_json_{index}") value).run' {}
    let name := base ++ Name.mkSimple s!"_mir_json_{index}"
    addSharedDefinition name (mkConst ``Json) value
    shared := shared.insert node (mkConst name)
  return shared

/-- Import a decoded document as a closed, kernel-checked Lean value.
`executionInput` records structural readiness only. Unsupported semantics stay
in the document's obligations; this command never produces a safety theorem. -/
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
      let shared ← quoteSharedJson declName result.document.sharedNodes
      letI : ToExpr Json := { toTypeExpr := mkConst ``Json, toExpr := jsonExpr shared }
      letI : ToExpr Input.TypedValue := {
        toTypeExpr := mkConst ``Input.TypedValue
        toExpr := fun value => (typedValueExpr value).run' {}
      }
      (splitValue declName (toExpr result)).run' {}
    liftCoreM <| withOptions (Elab.async.set · false) <| addAndCompile <| .defnDecl {
      name := declName
      levelParams := []
      type := mkConst ``Input.DecodeResult
      value := value
      hints := .regular 0
      safety := .safe
    }

end Miri.Frontend
