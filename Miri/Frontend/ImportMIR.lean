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

deriving instance ToExpr for MIR.IntegerKind
deriving instance ToExpr for MIR.BinOp
deriving instance ToExpr for MIR.UnOp
deriving instance ToExpr for ABI.ExternAbi
deriving instance ToExpr for MIR.Location
deriving instance ToExpr for MIR.SpanRef
deriving instance ToExpr for MIR.Mutability
deriving instance ToExpr for MIR.Safety
deriving instance ToExpr for MIR.Variance
deriving instance ToExpr for MIR.PointerCoercion
deriving instance ToExpr for MIR.CoercionSource
deriving instance ToExpr for MIR.CastKind
deriving instance ToExpr for MIR.FakeBorrowKind
deriving instance ToExpr for MIR.MutBorrowKind
deriving instance ToExpr for MIR.BorrowKind
deriving instance ToExpr for MIR.RawPtrKind
deriving instance ToExpr for MIR.WithRetag
deriving instance ToExpr for MIR.RuntimeChecks
deriving instance ToExpr for MIR.LoopHintAttr
deriving instance ToExpr for MIR.FakeReadCause
deriving instance ToExpr for MIR.CallSource
deriving instance ToExpr for MIR.InlineAsmMacro
deriving instance ToExpr for MIR.UnwindTerminateReason
deriving instance ToExpr for MIR.UnwindAction
deriving instance ToExpr for MIR.CoroutineSource
deriving instance ToExpr for MIR.CoroutineDesugaring
deriving instance ToExpr for MIR.Movability
deriving instance ToExpr for MIR.CoroutineKind
deriving instance ToExpr for MIR.HirId
deriving instance ToExpr for MIR.CoveragePointKind
deriving instance ToExpr for MIR.CoverageKind
deriving instance ToExpr for MIR.BackwardIncompatibleDropReason
deriving instance ToExpr for MIR.ProjectionKind
deriving instance ToExpr for MIR.UserTypeProjection
deriving instance ToExpr for MIR.AnalysisPhase
deriving instance ToExpr for MIR.RuntimePhase
deriving instance ToExpr for MIR.MirPhase
deriving instance ToExpr for MIR.ConstPointer
deriving instance ToExpr for MIR.ScalarValue
deriving instance ToExpr for MIR.ConstValue
deriving instance ToExpr for MIR.ConstAliasKind
deriving instance ToExpr for MIR.ConstExpressionCastKind
deriving instance ToExpr for MIR.ConstExpressionKind
deriving instance ToExpr for MIR.BoundVarIndexKind
deriving instance ToExpr for MIR.BoundRegionKind
deriving instance ToExpr for MIR.BoundTypeKind
deriving instance ToExpr for MIR.BoundVariableKind
deriving instance ToExpr for MIR.LateParamRegionKind
deriving instance ToExpr for MIR.Region
deriving instance ToExpr for MIR.GenericArg
deriving instance ToExpr for MIR.ValTreeNode
deriving instance ToExpr for MIR.ValTree
deriving instance ToExpr for MIR.TypeConst
deriving instance ToExpr for MIR.MirConst
deriving instance ToExpr for MIR.ConstOperand
deriving instance ToExpr for MIR.ProjectionElem
deriving instance ToExpr for MIR.Place
deriving instance ToExpr for MIR.Operand
deriving instance ToExpr for MIR.CopyNonOverlapping
deriving instance ToExpr for MIR.NonDivergingIntrinsic
deriving instance ToExpr for MIR.AggregateKind
deriving instance ToExpr for MIR.Rvalue
deriving instance ToExpr for MIR.StatementKind
deriving instance ToExpr for MIR.SwitchTarget
deriving instance ToExpr for MIR.SwitchTargets
deriving instance ToExpr for MIR.SpannedOperand
deriving instance ToExpr for MIR.InlineAsmOptions
deriving instance ToExpr for MIR.InlineAsmTemplatePiece
deriving instance ToExpr for MIR.InlineAsmArch
deriving instance ToExpr for MIR.InlineAsmRegOrRegClass
deriving instance ToExpr for MIR.InlineAsmOperand
deriving instance ToExpr for MIR.InlineAsmTerminator
deriving instance ToExpr for MIR.AssertKind
deriving instance ToExpr for MIR.TerminatorKind
deriving instance ToExpr for MIR.SourceInfo
deriving instance ToExpr for MIR.Statement
deriving instance ToExpr for MIR.Terminator
deriving instance ToExpr for MIR.BasicBlock
deriving instance ToExpr for MIR.Body
deriving instance ToExpr for Interpreter.CallReifyReason
deriving instance ToExpr for Interpreter.CallShimKind
deriving instance ToExpr for Interpreter.CallInstanceKind
deriving instance ToExpr for Input.TypeShapeKind
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
deriving instance ToExpr for Input.ArmCallKind
deriving instance ToExpr for Input.InterruptCallKind
deriving instance ToExpr for Input.X86CallKind
deriving instance ToExpr for Input.CanonicalAbiKind
deriving instance ToExpr for Input.CanonicalAbi
deriving instance ToExpr for Input.FunctionSignature
deriving instance ToExpr for Input.CompilerPattern
deriving instance ToExpr for Input.ReprInteger
deriving instance ToExpr for Input.ScalableElement
deriving instance ToExpr for Input.ReprOptions
deriving instance ToExpr for Input.AdtField
deriving instance ToExpr for Input.AdtVariant
deriving instance ToExpr for Input.AdtShape
deriving instance ToExpr for Input.ArrayConstructor
deriving instance ToExpr for Input.AliasTypeKind
deriving instance ToExpr for Input.TypeShape
deriving instance ToExpr for Input.AdtCompilerFacts
deriving instance ToExpr for Input.ProjectionField
deriving instance ToExpr for Input.ProjectionParent
deriving instance ToExpr for Input.ProjectionQueries
deriving instance ToExpr for Input.DiscriminantValue
deriving instance ToExpr for Input.DiscriminantInfo
deriving instance ToExpr for Input.TypeCompilerFacts
deriving instance ToExpr for Input.TypeNode
deriving instance ToExpr for Input.InitRange
deriving instance ToExpr for Input.Relocation
deriving instance ToExpr for Input.MemoryMutability
deriving instance ToExpr for Input.AllocationBytes
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
deriving instance ToExpr for Input.SourceAllocIdKind
deriving instance ToExpr for Input.SourceAllocIdStatus
deriving instance ToExpr for Input.SourceAllocIdPoolRow
deriving instance ToExpr for Input.SourceAllocIdDedupKind
deriving instance ToExpr for Input.SourceAllocIdSaltResult
deriving instance ToExpr for Input.SourceAllocIdDedupRow
deriving instance ToExpr for Input.CompilerAllocIdWorld
deriving instance ToExpr for Input.CallResolutionKind
deriving instance ToExpr for Input.CallResolutionEvidence
deriving instance ToExpr for Input.InlinedScope
deriving instance ToExpr for Input.SourceScope
deriving instance ToExpr for Input.CompilerSourcePosition
deriving instance ToExpr for Input.BacktraceSpan
deriving instance ToExpr for Input.LocalDecl
deriving instance ToExpr for Input.ThreadLocalEvidence
deriving instance ToExpr for Input.PlaceFact
deriving instance ToExpr for Input.DynamicUpcastEvidence
deriving instance ToExpr for Input.NodeFacts
deriving instance ToExpr for Input.BodyCore
deriving instance ToExpr for Input.PromotedBody
deriving instance ToExpr for Input.Body
deriving instance ToExpr for Input.BodyRoot
deriving instance ToExpr for Input.InstanceNode
deriving instance ToExpr for Input.ScopeRoot
deriving instance ToExpr for Input.SelectedScope
deriving instance ToExpr for Input.TargetPointerSpec
deriving instance ToExpr for Input.TargetAddressSpace
deriving instance ToExpr for Input.TargetDataLayoutEvidence
deriving instance ToExpr for Input.CompilerPredicateEvidence
deriving instance ToExpr for Input.Catalog.Signature
deriving instance ToExpr for Input.Catalog.Artifact
deriving instance ToExpr for Input.Catalog.ProducerSettings
deriving instance ToExpr for Input.Catalog.Session
deriving instance ToExpr for Input.Catalog.IntrinsicMetadata
deriving instance ToExpr for Input.Catalog.TargetFeature
deriving instance ToExpr for Input.Catalog.RuntimeInstance
deriving instance ToExpr for Input.Catalog.RuntimeType
deriving instance ToExpr for Input.Catalog.VtableRef
deriving instance ToExpr for Input.Catalog.RuntimeVirtual
deriving instance ToExpr for Input.Catalog.Startup
deriving instance ToExpr for Input.Catalog.ImportLinkage
deriving instance ToExpr for Input.Catalog.ExternDeclaration
deriving instance ToExpr for Input.Catalog.ForeignCandidate
deriving instance ToExpr for Input.Catalog.SelectedExport
deriving instance ToExpr for Input.Catalog.ForeignFallback
deriving instance ToExpr for Input.Catalog.AllocatorTarget
deriving instance ToExpr for Input.Catalog.ForeignSymbols
deriving instance ToExpr for Input.Catalog.Runtime
deriving instance ToExpr for Input.Catalog.FrameMetadata
deriving instance ToExpr for Input.Catalog.InstanceAbi
deriving instance ToExpr for Input.Catalog.FunctionType
deriving instance ToExpr for Input.Catalog.PointerAbi
deriving instance ToExpr for Input.Catalog.HelperSignature
deriving instance ToExpr for Input.Catalog.FunctionFacts
deriving instance ToExpr for Input.Catalog.CastQuery
deriving instance ToExpr for Input.Catalog.TypeName
deriving instance ToExpr for Input.Catalog.CallerLocation
deriving instance ToExpr for Input.Catalog.PanicQuery
deriving instance ToExpr for Input.Catalog.NativeSignature
deriving instance ToExpr for Input.Catalog.RetagQuery
deriving instance ToExpr for Input.Catalog.CovarianceQuery
deriving instance ToExpr for Input.Catalog.GlobalByteCandidate
deriving instance ToExpr for Input.Catalog.GlobalBytes
deriving instance ToExpr for Input.Catalog.StartResolution
deriving instance ToExpr for Input.Catalog.EntrySignature
deriving instance ToExpr for Input.Catalog.MainEntry
deriving instance ToExpr for Input.Catalog.CompilerEntry
deriving instance ToExpr for Input.Catalog.LinkSection
deriving instance ToExpr for Input.Catalog.Main
deriving instance ToExpr for Input.Catalog.Primitives
deriving instance ToExpr for Input.Catalog.VtableQuery
deriving instance ToExpr for Input.Catalog.ShimSignature
deriving instance ToExpr for Input.Catalog.ShimAbi
deriving instance ToExpr for Input.Catalog.NamedShimAbi
deriving instance ToExpr for Input.Catalog.TypeLayouts
deriving instance ToExpr for Input.Catalog.NamedConstant
deriving instance ToExpr for Input.Catalog.NamedStatic
deriving instance ToExpr for Input.Catalog.Queries
deriving instance ToExpr for Input.ImportDocument
deriving instance ToExpr for Input.ExecutionInput

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
