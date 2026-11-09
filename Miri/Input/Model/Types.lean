import Lean
import Miri.Memory.CtfeProvenance
import Miri.MIR.Operators
import Miri.Interpreter.Instance

/-!
Typed data model for the pinned rustc MIR export.  These structures describe
compiler input only; successful decoding is not a
claim that Lean has implemented the corresponding Miri operation.
-/

namespace Miri.Input

abbrev TypeId := Nat
abbrev AllocationId := Nat
abbrev InstanceId := Nat
abbrev LayoutId := Nat
abbrev FunctionAbiId := Nat
abbrev SpanId := Nat
abbrev DefinitionRef := Nat
abbrev TypeConstantId := Nat
abbrev BodyId := Nat
abbrev PredicateId := Nat
abbrev LocalId := Nat
abbrev BlockId := Nat

inductive TypeShapeKind where
  | bool | char | int | uint | float | adt | foreign | str | array
  | patternType | slice | rawPointer | reference | functionDefinition
  | functionPointer | unsafeBinder | dynamicTraitObject | closure
  | coroutineClosure | coroutine | never | tuple
  | alias
  deriving Repr, DecidableEq

inductive StatementVariant where
  | assign | fakeRead | setDiscriminant | storageLive | storageDead
  | placeMention | ascribeUserType | coverage | intrinsic
  | constEvalCounter | nop | backwardIncompatibleDropHint
  deriving Repr, DecidableEq

inductive TerminatorVariant where
  | goto | switchInt | unwindResume | unwindTerminate | return
  | unreachable | drop | call | tailCall | assert | yield
  | coroutineDrop | falseEdge | falseUnwind | inlineAsm
  deriving Repr, DecidableEq

inductive RvalueVariant where
  | use | repeat | ref | threadLocalRef | rawPtr | cast | binaryOp
  | unaryOp | discriminant | aggregate | copyForDeref
  | wrapUnsafeBinder | reborrow
  deriving Repr, DecidableEq

inductive OperandVariant where
  | copy | move | constant | runtimeChecks
  deriving Repr, DecidableEq

inductive ProjectionVariant where
  | deref | field | index | constantIndex | subslice | downcast
  | opaqueCast | unwrapUnsafeBinder | phantomDeref
  deriving Repr, DecidableEq

inductive LayoutKind where
  | layout
  deriving Repr, DecidableEq

inductive LayoutVariantsKind where
  | single | multiple | empty
  deriving Repr, DecidableEq

inductive BackendReprKind where
  | scalar | scalarPair | memory | simdVector | scalableSimdVector
  deriving Repr, DecidableEq

inductive FieldShapeKind where
  | primitive | union | array | arbitrary
  deriving Repr, DecidableEq

inductive IntegerTypeTag where
  | known (kind : Miri.MIR.IntegerKind)
  deriving Repr, DecidableEq

inductive FloatTypeTag where
  | f16 | f16b | f32 | f64 | f128 | ppcf128
  deriving Repr, DecidableEq

inductive AdtKind where
  | structKind | unionKind | enumKind
  deriving Repr, DecidableEq

structure TypeShapeMetadata where
  signedKind : Option IntegerTypeTag
  unsignedKind : Option IntegerTypeTag
  floatKind : Option FloatTypeTag
  adtKind : Option AdtKind
  deriving Repr, DecidableEq

inductive PrimitiveKind where
  | integer | float | pointer
  deriving Repr, DecidableEq

inductive ScalarShapeKind where
  | initialized | union
  deriving Repr, DecidableEq


inductive PassModeKind where
  | ignore | direct | pair | cast | indirect | indirectUnsized
  deriving Repr, DecidableEq

inductive AllocationKind where
  | memory | function | static | vtable | typeId
  deriving Repr, DecidableEq

inductive InstanceKind where
  | instanceMir | intrinsicDispatch
  | foreignItemNoMir
  | virtualDispatchTarget
  | identityOnly
  deriving Repr, DecidableEq

structure Obligation where
  path : String
  message : String
  deriving Repr, DecidableEq

/-- Exact source coordinate payload emitted by the pinned rustc span exporter.
`file` and `context` retain the compiler's diagnostic spellings; no consumer
should parse them to recover instruction semantics. -/
structure SourcePosition where
  line : Nat
  column : Nat
  deriving Repr, DecidableEq

structure SourceSpanData where
  isDummy : Bool := false
  originalPayload : String
  lo : Nat
  hi : Nat
  start : SourcePosition
  «end» : SourcePosition
  context : String
  file : String
  deriving Repr, DecidableEq

structure SourceInfo where
  spanId : SpanId
  scope : Nat
  deriving Repr, DecidableEq

structure Producer where
  miriCommit : String
  rustcCommit : String
  rustcVersion : String
  targetTriple : String
  deriving Repr, DecidableEq

structure TaggedNode where
  tag : String
  -- Kept for round-tripping and diagnostics.  Semantic consumers must use the
  -- typed tags and explicitly decoded children, never inspect debug text.
  payload : Lean.Json
  deriving BEq

structure FieldShape where
  kind : FieldShapeKind
  fieldCount : Nat
  offsetBytes : Option Nat
  strideBytes : Option Nat
  offsetsBytes : Array Nat
  memoryOrder : Array Nat
  payload : Lean.Json

structure PrimitiveLayout where
  kind : PrimitiveKind
  sizeBytes : Nat
  integerKind : Option IntegerTypeTag
  signed : Option Bool
  floatKind : Option FloatTypeTag
  addressSpace : Option Nat
  payload : Lean.Json

structure ScalarLayout where
  kind : ScalarShapeKind
  primitive : PrimitiveLayout
  validRange : Option (Nat × Nat)
  payload : Lean.Json

structure NicheLayout where
  offsetBytes : Nat
  primitive : PrimitiveLayout
  validRange : Nat × Nat

structure BackendRepr where
  kind : BackendReprKind
  sized : Option Bool
  scalar : Option ScalarLayout
  first : Option ScalarLayout
  second : Option ScalarLayout
  secondOffsetBytes : Option Nat
  element : Option ScalarLayout
  laneCount : Option Nat
  vectorCount : Option Nat
  payload : Lean.Json

structure LayoutVariant where
  fields : FieldShape
  largestNiche : Option NicheLayout
  variantIndex : Nat
  sizeBytes : Nat
  backendRepr : BackendRepr
  fieldOffsetsBytes : Array Nat
  uninhabited : Bool
  payload : Lean.Json

inductive TagEncodingKind where
  | direct | niche
  deriving Repr, DecidableEq

structure TagEncoding where
  kind : TagEncodingKind
  untaggedVariant : Option Nat
  nicheVariants : Option (Nat × Nat)
  nicheStart : Option Nat
  payload : Lean.Json

structure VariantsLayout where
  kind : LayoutVariantsKind
  variantIndex : Option Nat
  tag : Option ScalarLayout
  tagEncoding : Option TagEncoding
  tagFieldIndex : Option Nat
  variants : Array LayoutVariant
  payload : Lean.Json

structure Layout where
  maxReprAlignBytes : Option Nat
  reprC : Bool
  uninhabited : Bool
  largestNiche : Option NicheLayout
  randomizationSeed : Nat
  kind : LayoutKind
  sizeBytes : Option Nat
  abiAlignBytes : Option Nat
  unadjustedAbiAlignBytes : Option Nat
  fieldOffsetsBytes : Array Nat
  fields : Option FieldShape
  variantsLayout : Option VariantsLayout
  backendRepresentation : Option BackendRepr
  variantsKind : Option LayoutVariantsKind
  backendReprKind : Option BackendReprKind
  variants : Option TaggedNode
  backendRepr : Option TaggedNode
  payload : Lean.Json

structure ExternAbi where
  kind : TaggedNode
  unwind : Option Bool
  sourceSpelling : Option String
  payload : Lean.Json

inductive ArmCallKind where
  | aapcs | cmseNonSecureCall | cmseNonSecureEntry
  deriving Repr, DecidableEq

inductive InterruptCallKind where
  | avr | avrNonBlocking | msp430 | riscvMachine | riscvSupervisor | x86
  deriving Repr, DecidableEq

inductive X86CallKind where
  | fastcall | stdcall | sysv64 | thiscall | vectorcall | win64
  deriving Repr, DecidableEq

inductive CanonicalAbiKind where
  | c | rust | rustCold | rustPreserveNone | rustTail | custom | swift
  | arm | gpuKernel | interrupt | x86
  deriving Repr, DecidableEq

structure CanonicalAbi where
  kind : CanonicalAbiKind
  armCall : Option ArmCallKind
  interruptKind : Option InterruptCallKind
  x86Call : Option X86CallKind
  payload : Lean.Json

inductive TypedEnumTag where
  | safety | borrowKind | fakeBorrowKind | mutBorrowKind | mutability
  | castKind | pointerCoercion | coercionSource | unwindReason
  | aggregateKind | unwindAction
  | mirPhase | mirPhaseStage | withRetag | runtimeCheck | fakeReadCause
  | callSource | backwardDropReason | regionKind | boundRegionKind
  | boundVarIndexKind | lateParamRegionKind | integerType | floatType | adtKind
  | variance | coverageKind | coveragePointKind | fakeBorrowRetagMode | typeConstKind
  deriving Repr, DecidableEq, Hashable

inductive UserTypeProjectionKind where
  | deref
  | field (index : Nat)
  | index
  | constantIndex (offset minLength : Nat) (fromEnd : Bool)
  | subslice (startIndex endIndex : Nat) (fromEnd : Bool)
  | downcast (name : Option String) (variantIndex : Nat)
  | opaqueCast
  | unwrapUnsafeBinder
  | phantomDeref
  deriving Repr, DecidableEq

structure UserTypeProjection where
  baseIndex : Option Nat
  projections : Option (Array UserTypeProjectionKind)
  payload : Lean.Json
  deriving BEq

structure FunctionSignature where
  inputs : Array TypeId
  output : TypeId
  safety : TaggedNode
  abi : ExternAbi
  cVariadic : Bool


inductive CompilerPattern where
  | range (start finish : TypeConstantId)
  | or (patterns : Array CompilerPattern)
  | notNull

inductive ReprInteger where
  | pointerSized (signed : Bool)
  | fixed (kind : IntegerTypeTag) (sizeBits : Nat) (signed : Bool)
  deriving Repr, DecidableEq

inductive ScalableElement where
  | elementCount (count : Nat)
  | container
  deriving Repr, DecidableEq

structure ReprOptions where
  integer : Option ReprInteger
  alignBytes : Option Nat
  packBytes : Option Nat
  simd : Bool
  c : Bool
  rust : Bool
  packed : Bool
  transparent : Bool
  linear : Bool
  scalable : Bool
  flagsBits : Nat
  scalableElement : Option ScalableElement
  canRandomizeTypeLayout : Bool
  inhibitEnumLayoutOptimization : Bool
  inhibitStructFieldReordering : Bool
  inhibitNewtypeAbiOptimization : Bool
  fieldShuffleSeed : Nat
  deriving Repr, DecidableEq

structure AdtField where
  index : Nat
  name : String
  typeId : TypeId
  deriving Repr, DecidableEq

structure AdtVariant where
  index : Nat
  name : String
  fields : Array AdtField
  deriving Repr, DecidableEq

structure AdtShape where
  definition : DefinitionRef
  kind : AdtKind
  representation : ReprOptions
  args : Array Miri.MIR.GenericArg
  variants : Array AdtVariant
  deriving Repr, DecidableEq

structure ArrayConstructor where
  count : Nat
  canonicalValueConstructor : Bool
  deriving Repr, DecidableEq

inductive AliasTypeKind where
  | projection | inherent | opaque | free
  deriving Repr, DecidableEq

inductive TypeShape where
  | bool | char
  | int (kind : IntegerTypeTag)
  | uint (kind : IntegerTypeTag)
  | float (kind : FloatTypeTag)
  | adt (data : AdtShape)
  | foreign (definition : DefinitionRef)
  | str
  | array (element : TypeId) (length : TypeConstantId) (constructor : ArrayConstructor)
  | patternType (base : TypeId) (pattern : CompilerPattern)
  | slice (element : TypeId)
  | rawPointer (pointee : TypeId) (mutability : Miri.MIR.Mutability)
  | reference (pointee : TypeId) (mutability : Miri.MIR.Mutability) (region : Miri.MIR.Region)
  | functionDefinition (definition : DefinitionRef) (args : Array Miri.MIR.GenericArg)
      (signature : FunctionSignature) (boundVariables : Array Miri.MIR.BoundVariableKind)
  | functionPointer (signature : FunctionSignature) (boundVariables : Array Miri.MIR.BoundVariableKind)
  | unsafeBinder (inner : TypeId) (boundVariables : Array Miri.MIR.BoundVariableKind)
  | dynamicTraitObject (predicates : Array PredicateId) (principal : Option PredicateId) (region : Miri.MIR.Region)
  | closure (definition : DefinitionRef) (args : Array Miri.MIR.GenericArg) (upvarCount : Nat)
  | coroutineClosure (definition : DefinitionRef) (args : Array Miri.MIR.GenericArg)
  | coroutine (definition : DefinitionRef) (args : Array Miri.MIR.GenericArg)
  | never
  | tuple (elements : Array TypeId)
  | alias (kind : AliasTypeKind) (definition : DefinitionRef) (args : Array Miri.MIR.GenericArg)

namespace TypeShape

def kind : TypeShape → TypeShapeKind
  | .bool => .bool | .char => .char | .int _ => .int | .uint _ => .uint
  | .float _ => .float | .adt _ => .adt | .foreign _ => .foreign | .str => .str
  | .array .. => .array | .patternType .. => .patternType | .slice _ => .slice
  | .rawPointer .. => .rawPointer | .reference .. => .reference
  | .functionDefinition .. => .functionDefinition | .functionPointer .. => .functionPointer
  | .unsafeBinder .. => .unsafeBinder | .dynamicTraitObject .. => .dynamicTraitObject
  | .closure .. => .closure | .coroutineClosure .. => .coroutineClosure | .coroutine .. => .coroutine
  | .never => .never | .tuple _ => .tuple | .alias .. => .alias

def metadata (shape : TypeShape) : TypeShapeMetadata := {
  signedKind := match shape with | .int k => some k | _ => none
  unsignedKind := match shape with | .uint k => some k | _ => none
  floatKind := match shape with | .float k => some k | _ => none
  adtKind := match shape with | .adt data => some data.kind | _ => none }

def signature : TypeShape → Option FunctionSignature
  | .functionDefinition _ _ signature _ | .functionPointer signature _ => some signature
  | _ => none

def pattern : TypeShape → Option CompilerPattern
  | .patternType _ pattern => some pattern
  | _ => none

end TypeShape

structure AdtCompilerFacts where
  definitionId : DefinitionRef
  itemName : String
  nonnullOptimizationGuaranteed : Bool

structure ProjectionField where
  index : Nat
  typeId : TypeId
  layoutId : LayoutId

structure ProjectionParent where
  variant : Option Nat
  layoutId : LayoutId
  fields : Array ProjectionField

structure ProjectionQueries where
  typingEnvironment : String
  parents : Array ProjectionParent

structure DiscriminantValue where
  variant : Nat
  typeId : TypeId
  bits : Nat

structure DiscriminantInfo where
  hasDiscriminants : Bool
  adtVariantCount : Option Nat
  values : Array DiscriminantValue

structure TypeCompilerFacts where
  typingEnvironment : String
  inputTypeId : TypeId
  queryInputTypeId : TypeId := 0
  booleanQueries : Array (String × Bool)
  typeQueries : Array (String × Option TypeId)
  adt : Option AdtCompilerFacts := none
  definitionId : Option DefinitionRef := none
  projectionQueries : Option ProjectionQueries := none
  simdSizeAndType : Option (Nat × TypeId) := none
  discriminants : Option DiscriminantInfo := none
  typeIdHash : Option Nat := none
  captureNames : Option (Array (Option String)) := none

structure TypeNode where
  layoutQueryInputTypeId : Option TypeId := none
  compilerFacts : Option TypeCompilerFacts := none
  id : TypeId
  display : String
  shape : TypeShape
  layoutId : LayoutId

namespace TypeNode

def shapeKind (node : TypeNode) : TypeShapeKind := node.shape.kind

def shapeMetadata (node : TypeNode) : TypeShapeMetadata := node.shape.metadata

def signature (node : TypeNode) : Option FunctionSignature := node.shape.signature

def pattern (node : TypeNode) : Option CompilerPattern := node.shape.pattern

end TypeNode

structure InitRange where
  initialized : Bool
  startBytes : Nat
  endBytesExclusive : Nat
  deriving Repr, DecidableEq

structure Relocation where
  storageOffsetBytes : Nat
  target : AllocationId
  targetOffsetEncodedBytes : String
  immutable : Bool
  sharedRef : Bool
  ctfeProvenance : Miri.Memory.CtfeProvenance
  deriving Repr, DecidableEq


inductive MemoryMutability where
  | mutable | immutable
  deriving Repr, DecidableEq

structure AllocationMemory where
  sizeBytes : Nat
  alignBytes : Nat
  mutability : MemoryMutability
  bytesHex : String
  initializationRanges : Array InitRange
  relocations : Array Relocation
  deriving Repr, DecidableEq

inductive ArgumentExtensionKind where
  | none | zeroExtend | signExtend
  deriving Repr, DecidableEq

inductive ArgumentCaptureKind where
  | none | address | readOnly | unrestricted
  deriving Repr, DecidableEq

inductive IndirectModeKind where
  | pointer | onStack | amdgpuKernelArgument
  deriving Repr, DecidableEq

structure AbiAttributes where
  noAlias : Bool
  noFree : Bool
  noUndef : Bool
  nonNull : Bool
  readOnly : Bool
  writable : Bool
  inRegister : Bool
  regularBits : Nat
  pointeeSizeBytes : Nat
  pointeeAlignBytes : Option Nat
  argExtension : ArgumentExtensionKind
  captures : ArgumentCaptureKind

inductive AbiRegisterKind where
  | integer | float | ppcF128 | vector
  deriving Repr, DecidableEq

inductive AbiRegisterHint where
  | integer (kind : IntegerTypeTag) (signed : Bool)
  | float (kind : FloatTypeTag)
  | pointer (addressSpace : Nat)
  deriving Repr, DecidableEq

structure AbiRegister where
  kind : AbiRegisterKind
  sizeBits : Nat
  hintElement : Option AbiRegisterHint
  payload : Lean.Json

structure AbiCastTarget where
  prefixRegisters : Array AbiRegister
  restOffsetBytes : Option Nat
  restRegister : AbiRegister
  restTotalBytes : Nat
  restIsConsecutive : Bool
  attributes : AbiAttributes
  payload : Lean.Json

structure AbiPassMode where
  kind : PassModeKind
  attributes : Array AbiAttributes
  castTarget : Option AbiCastTarget
  padI32Count : Option Nat
  addressSpace : Option Nat
  indirectMode : Option IndirectModeKind
  payload : Lean.Json

structure AbiArgument where
  typeId : TypeId
  /-- Physical compiler TyAndLayout for this FnAbi argument. The logical type
  remains `typeId`; Rust can adjust the ABI layout independently (notably the
  forced-thin virtual-call receiver). The input schema validates its presence. -/
  layoutId : LayoutId
  mode : AbiPassMode
  payload : Lean.Json

structure FunctionAbi where
  arguments : Array AbiArgument
  returnValue : AbiArgument
  callingConvention : CanonicalAbi
  canUnwind : Bool
  cVariadic : Bool
  fixedCount : Nat
  payload : Lean.Json

inductive TypedValue where
  | scalar (value : Lean.Json)
  | diagnostic (value : Lean.Json)
  | array (values : Array TypedValue)
  | object (fields : Array (String × TypedValue))
  | typeRef (id : TypeId)
  | allocationRef (id : AllocationId)
  | instanceRef (id : InstanceId)
  | localRef (id : LocalId)
  | blockRef (id : BlockId)
  | sourceSpan (id : SpanId)
  | sourceInfo (value : SourceInfo)
  | statement (variant : StatementVariant)
      (fields : Array (String × TypedValue))
  | terminator (variant : TerminatorVariant)
      (fields : Array (String × TypedValue))
  | rvalue (variant : RvalueVariant)
      (fields : Array (String × TypedValue))
  | binOperator (operator : Miri.MIR.BinOp)
  | unOperator (operator : Miri.MIR.UnOp)
  | enumTag (category : TypedEnumTag) (tag : TaggedNode)
      (children : Array (String × TypedValue))
  | userTypeProjection (value : UserTypeProjection)
  | operand (variant : OperandVariant)
      (fields : Array (String × TypedValue))
  | projection (variant : ProjectionVariant)
      (fields : Array (String × TypedValue))
  deriving BEq


structure DefinitionId where
  crateIndex : Nat
  index : Nat
  deriving Repr, DecidableEq

inductive VtableEntryKind where
  | dropInPlaceNull | dropInPlace | sizeBytes | alignBytes | vacant
  | method | supertraitVtablePointer
  deriving Repr, DecidableEq

inductive VtablePredicateKind where
  | trait | autoTrait | projection
  deriving Repr, DecidableEq

structure FunctionAllocation where
  instanceId : InstanceId
  payload : Lean.Json
  deriving BEq

/-- Exact compiler GlobalAlloc::Static metadata queries, independent of
initializer evaluation and runtime allocation adjustment. -/
structure StaticGlobalInfo where
  nested : Bool
  sizeBytes : Nat
  alignBytes : Nat
  mutability : MemoryMutability
  isStatic : Bool
  foreignItem : Bool
  threadLocal : Bool
  payload : Lean.Json
  deriving BEq

structure StaticAllocation where
  globalInfo : Option StaticGlobalInfo := none
  definitionId : DefinitionRef
  definitionPath : String
  threadLocal : Bool
  initializer : Option AllocationMemory
  payload : Lean.Json
  deriving BEq

structure VtablePredicate where
  kind : VtablePredicateKind
  definitionId : DefinitionRef
  definitionPath : Option String
  genericArgs : Array Miri.MIR.GenericArg
  boundVariables : Array Miri.MIR.BoundVariableKind
  projectionTerm : Option TypeId
  payload : Lean.Json
  deriving BEq

structure VtableEntry where
  kind : VtableEntryKind
  instanceId : Option InstanceId
  allocationId : Option AllocationId
  traitDefinitionId : Option DefinitionRef
  traitDefinitionPath : Option String
  payload : Lean.Json
  deriving BEq

structure VtableAllocation where
  principalPredicate : Option PredicateId
  typeId : TypeId
  sizeBytes : Option Nat
  alignBytes : Option Nat
  predicates : Array PredicateId
  entries : Array VtableEntry
  payload : Lean.Json
  deriving BEq

inductive AllocationData where
  | memory (value : AllocationMemory)
  | function (value : FunctionAllocation)
  | static (value : StaticAllocation)
  | vtable (value : VtableAllocation)
  | typeId (value : TypeId)
  deriving BEq

structure AllocationNode where
  id : AllocationId
  /-- Exact rustc `AllocId.0.get()` witness supplied by the pinned exporter.
  Optional without a captured allocator world; never inferred from `id`. -/
  sourceAllocId : Option UInt64 := none
  kind : AllocationKind
  memory : Option AllocationMemory
  data : Option AllocationData
  payload : Lean.Json
  deriving BEq

/-- The optional prepared post-export rustc allocator snapshot. Raw rustc IDs
remain separate from exporter graph IDs and from the runtime's dense IDs. -/
inductive SourceAllocIdKind where
  | dangling | memory | function | vtable | static | typeId
  deriving Repr, DecidableEq

inductive SourceAllocIdStatus where
  | dangling | serialized | opaque
  deriving Repr, DecidableEq

structure SourceAllocIdPoolRow where
  sourceAllocId : UInt64
  kind : SourceAllocIdKind
  status : SourceAllocIdStatus
  allocationId : Option AllocationId
  memoryMutability : Option MemoryMutability := none
  memoryAlignBytes : Option Nat := none
  memoryAllBytesInitialized : Option Bool := none
  memoryHasProvenance : Option Bool := none
  byteImageHex : Option String := none
  deriving Repr, DecidableEq

inductive SourceAllocIdDedupKind where
  | function | vtable | static | typeId | memory | bytes
  deriving Repr, DecidableEq

inductive SourceAllocIdProbeOutcome where
  | preexistingHit | missReservedByProbe
  deriving Repr, DecidableEq

structure SourceAllocIdSaltResult where
  salt : Nat
  allocationId : AllocationId
  sourceAllocId : UInt64
  outcome : SourceAllocIdProbeOutcome
  deriving Repr, DecidableEq

structure SourceAllocIdDedupRow where
  keyKind : SourceAllocIdDedupKind
  keyAllocationId : AllocationId
  byteImageHex : Option String
  salts : Array SourceAllocIdSaltResult
  deriving Repr, DecidableEq

structure CompilerAllocIdWorld where
  lastReservedSourceAllocId : UInt64
  nextSourceAllocId : UInt64
  finalSentinelSourceAllocId : UInt64
  rawPool : Array SourceAllocIdPoolRow
  dedupCatalog : Array SourceAllocIdDedupRow
  completeKeyFamilies : Array SourceAllocIdDedupKind := #[]
  /-- Families carry exact selected-key outcomes, without claiming every possible key. -/
  nonExhaustiveKeyFamilies : Array SourceAllocIdDedupKind := #[]
  deriving Repr, DecidableEq

structure MirNode where
  value : TypedValue
  sourceInfo : SourceInfo

inductive CallResolutionKind where
  | direct | virtualDispatch | indirect
  deriving Repr, DecidableEq

structure CallResolutionEvidence where
  kind : CallResolutionKind
  instanceId : Option InstanceId
  functionType : Option TypeId
  dispatchSlot : Option Nat
  fnAbiId : FunctionAbiId
  payload : Lean.Json

structure InlinedScope where
  instanceId : InstanceId
  callsiteSpanId : SpanId
  requiresCallerLocation : Bool
  deriving Repr, DecidableEq

structure SourceScope where
  id : Nat
  parent : Option Nat
  spanId : SpanId
  inlined : Option InlinedScope
  inlinedParent : Option Nat
  deriving Repr, DecidableEq

structure CompilerSourcePosition where
  bytePosition : Nat
  line : Nat
  column : Nat
  filename : String
  deriving Repr, DecidableEq

structure BacktraceSpan where
  spanId : SpanId
  collapsedLo : Nat
  position : CompilerSourcePosition
  deriving Repr, DecidableEq

structure BasicBlock where
  callResolution : Option CallResolutionEvidence
  id : BlockId
  statements : Array MirNode
  terminator : MirNode
  cleanup : Bool
  payload : Lean.Json

structure LocalDecl where
  id : LocalId
  typeId : TypeId
  sourceInfo : SourceInfo
  payload : Lean.Json

inductive BodyInputPhase where
  | template | alreadyInstantiated
  deriving Repr, DecidableEq

structure RequiredConstantCheck where
  index : Nat
  spanId : SpanId
  normalizedOperand : TypedValue
  value : TypedValue

structure ConstantQueryContext where
  instanceId : InstanceId
  inputPhase : BodyInputPhase
  normalizationBodyId : BodyId
  requiredTypingEnvironment : String
  requiredChecks : Array RequiredConstantCheck

structure BodyCore where
  constantQueryContext : Option ConstantQueryContext := none
  requiredConsts : Option (Array TypedValue) := none
  spanId : SpanId
  preambleDefSpanId : SpanId
  backtraceSpans : Array BacktraceSpan
  /-- Source location for body-scoped compiler queries. -/
  sourcePath : String := ""
  defPath : String
  definitionId : Option DefinitionRef
  phase : TypedValue
  injectionPhase : Option TypedValue
  argumentCount : Nat
  spreadArgument : Option LocalId
  locals : Array LocalDecl
  blocks : Array BasicBlock
  sourceScopes : Option (Array SourceScope)
  payload : Lean.Json

structure PromotedBody where
  index : Nat
  bodyId : Option BodyId
  payload : Lean.Json

structure Body extends BodyCore where
  promotedBodies : Array PromotedBody

structure BodyRoot where
  bodyId : BodyId
  entryInstance : InstanceId
  definitionId : DefinitionRef
  defPath : String
  isStatic : Bool
  threadLocalStatic : Bool
  promotedBodies : Array PromotedBody
  payload : Lean.Json

structure InstanceNode where
  instanceKind : Miri.Interpreter.CallInstanceKind
  genericArgs : Array Miri.MIR.GenericArg
  id : InstanceId
  kind : InstanceKind
  defPath : Option String
  definitionId : Option DefinitionRef
  bodyInstantiation : Option TaggedNode
  bodyTemplateIsPolymorphic : Option Bool
  instanceArgsAreMonomorphic : Option Bool
  bodyId : Option BodyId
  promotedBodies : Array PromotedBody
  payload : Lean.Json

structure ScopeRoot where
  defPath : String
  definitionId : DefinitionRef
  deriving Repr, DecidableEq

structure SelectedScope where
  kind : String
  semantics : String
  roots : Array ScopeRoot
  payload : Lean.Json

/-- Compiler-query target layout evidence, retained independently of a runtime
layout validator. Missing evidence is not inferred from the target triple. -/
structure TargetDataLayoutEvidence where
  payload : Lean.Json

/-- Exact compiler existential-predicate identity, stable comparison rank and
late-bound-region-erasing normalization result under an explicit environment. -/
structure CompilerPredicateEvidence where
  id : Nat
  typingEnvironment : String
  stableKey : Nat
  autoTrait : Bool
  normalizedId : Option Nat
  original : PredicateId
  payload : Lean.Json


end Miri.Input
