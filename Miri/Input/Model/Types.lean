import Lean
import Miri.Memory.CtfeProvenance
import Miri.MIR.Operators
import Miri.ABI.ExternAbi
import Miri.ABI.FnAbi
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
  | initial | scalarRust | scalarSysvArgument | scalarSysvReturn
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
`file` indexes the document filename table; `context` retains the compiler's
diagnostic spelling. Neither carries instruction semantics. -/
structure SourcePosition where
  line : Nat
  column : Nat
  deriving Repr, DecidableEq

structure SourceSpanData where
  isDummy : Bool := false
  lo : Nat
  hi : Nat
  start : SourcePosition
  «end» : SourcePosition
  context : String
  file : Nat
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
  deriving BEq

structure FieldShape where
  kind : FieldShapeKind
  fieldCount : Nat
  offsetBytes : Option Nat
  strideBytes : Option Nat
  offsetsBytes : Array Nat
  memoryOrder : Array Nat

structure PrimitiveLayout where
  kind : PrimitiveKind
  sizeBytes : Nat
  integerKind : Option IntegerTypeTag
  signed : Option Bool
  floatKind : Option FloatTypeTag
  addressSpace : Option Nat

structure ScalarLayout where
  kind : ScalarShapeKind
  primitive : PrimitiveLayout
  validRange : Option (Nat × Nat)

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

structure LayoutVariant where
  fields : FieldShape
  largestNiche : Option NicheLayout
  variantIndex : Nat
  sizeBytes : Nat
  backendRepr : BackendRepr
  fieldOffsetsBytes : Array Nat
  uninhabited : Bool

inductive TagEncodingKind where
  | direct | niche
  deriving Repr, DecidableEq

structure TagEncoding where
  kind : TagEncodingKind
  untaggedVariant : Option Nat
  nicheVariants : Option (Nat × Nat)
  nicheStart : Option Nat

structure VariantsLayout where
  kind : LayoutVariantsKind
  variantIndex : Option Nat
  tag : Option ScalarLayout
  tagEncoding : Option TagEncoding
  tagFieldIndex : Option Nat
  variants : Array LayoutVariant

inductive LayoutFieldOffsets where
  | explicit (offsets : Array Nat)
  | arrayFormula (strideBytes count : Nat)
  deriving Repr, DecidableEq

namespace LayoutFieldOffsets

/-- Formula metadata is bounded without enumerating any array fields. The
last product bounds every permitted `stride * index`, including zero stride. -/
def validate (offsets : LayoutFieldOffsets) (shape : FieldShape) : Except String Unit := do
  match offsets with
  | .explicit values =>
    unless shape.fieldCount == values.size do throw "field shape count does not match field_offsets_bytes"
  | .arrayFormula stride count =>
    unless shape.kind == .array && shape.strideBytes == some stride && shape.fieldCount == count do
      throw "array offset formula does not match field shape"
    unless stride < 2^64 && count < 2^64 do throw "array offset formula exceeds u64"
    if count > 0 && stride * (count - 1) >= 2^64 then throw "array offset formula overflows u64"

end LayoutFieldOffsets

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
  fieldOffsetsBytes : LayoutFieldOffsets
  fields : Option FieldShape
  variantsLayout : Option VariantsLayout
  backendRepresentation : Option BackendRepr
  variantsKind : Option LayoutVariantsKind
  backendReprKind : Option BackendReprKind
  variants : Option TaggedNode
  backendRepr : Option TaggedNode
  primitiveRecipe : Option String := none

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
  deriving BEq

structure FunctionSignature where
  inputs : Array TypeId
  output : TypeId
  safety : Miri.MIR.Safety
  abi : Miri.ABI.ExternAbi
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
  flagsBits : Nat
  scalableElement : Option ScalableElement
  fieldShuffleSeed : Nat
  deriving Repr, DecidableEq

namespace ReprOptions

-- Pinned rustc_abi::ReprOptions keeps these properties in flags, int and pack.
def c (repr : ReprOptions) : Bool := repr.flagsBits &&& 1 != 0
def simd (repr : ReprOptions) : Bool := repr.flagsBits &&& 2 != 0
def transparent (repr : ReprOptions) : Bool := repr.flagsBits &&& 4 != 0
def linear (repr : ReprOptions) : Bool := repr.flagsBits &&& 8 != 0
def scalable (repr : ReprOptions) : Bool := repr.flagsBits &&& 64 != 0
def rust (repr : ReprOptions) : Bool := !repr.c && !repr.simd && !repr.scalable && !repr.transparent
def packed (repr : ReprOptions) : Bool := repr.packBytes.isSome
def inhibitEnumLayoutOptimization (repr : ReprOptions) : Bool := repr.c || repr.integer.isSome
def inhibitNewtypeAbiOptimization (repr : ReprOptions) : Bool := repr.c || repr.simd
def inhibitStructFieldReordering (repr : ReprOptions) : Bool :=
  repr.c || repr.simd || repr.scalable || repr.linear || repr.integer.isSome
def canRandomizeTypeLayout (repr : ReprOptions) : Bool :=
  !repr.inhibitStructFieldReordering && repr.flagsBits &&& 16 != 0

end ReprOptions

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

def decodeAllocationHex (hex : String) : Except String (Array UInt8) := do
  let chars := hex.toList.toArray
  unless chars.size % 2 == 0 do throw "odd hexadecimal byte count"
  let digit (c : Char) : Except String Nat :=
    if c ≥ '0' && c ≤ '9' then pure (c.toNat - '0'.toNat)
    else if c ≥ 'a' && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if c ≥ 'A' && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw "invalid hexadecimal allocation byte"
  let mut out := #[]
  for i in [:chars.size / 2] do
    let some hi := chars[2*i]? | throw "missing hexadecimal high nibble"
    let some lo := chars[2*i+1]? | throw "missing hexadecimal low nibble"
    out := out.push (UInt8.ofNat (16 * (← digit hi) + (← digit lo)))
  pure out

inductive AllocationBytes where
  | image (bytes : Array UInt8)
  | reference (id : Nat)
  deriving Repr, DecidableEq

def AllocationBytes.checkedBytes : AllocationBytes → Except String (Array UInt8)
  | .image bytes => pure bytes
  | .reference id => throw s!"unresolved allocation byte image {id}"

structure AllocationMemory where
  sizeBytes : Nat
  alignBytes : Nat
  mutability : MemoryMutability
  bytesHex : AllocationBytes
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
  regularBits : Nat
  pointeeSizeBytes : Nat
  pointeeAlignBytes : Option Nat
  argExtension : ArgumentExtensionKind
  deriving BEq

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
  deriving BEq

structure AbiCastTarget where
  prefixRegisters : Array AbiRegister
  restOffsetBytes : Option Nat
  restRegister : AbiRegister
  restTotalBytes : Nat
  restIsConsecutive : Bool
  attributes : AbiAttributes
  deriving BEq

structure AbiPassMode where
  kind : PassModeKind
  attributes : Array AbiAttributes
  castTarget : Option AbiCastTarget
  padI32Count : Option Nat
  addressSpace : Option Nat
  indirectMode : Option IndirectModeKind
  deriving BEq

structure AbiArgument where
  typeId : TypeId
  /-- Physical compiler TyAndLayout for this FnAbi argument. The logical type
  remains `typeId`; Rust can adjust the ABI layout independently (notably the
  forced-thin virtual-call receiver). The input schema validates its presence. -/
  layoutId : LayoutId
  mode : AbiPassMode
  deriving BEq

structure FunctionAbi where
  arguments : Array AbiArgument
  returnValue : AbiArgument
  callingConvention : CanonicalAbi
  unwindSeed : Miri.ABI.UnwindSeed
  cVariadic : Bool
  fixedCount : Nat
  deriving BEq

structure DefinitionId where
  crateIndex : Nat
  index : Nat
  bodyTrackCaller : Option Bool := none
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
  deriving BEq

structure StaticAllocation where
  globalInfo : Option StaticGlobalInfo := none
  definitionId : DefinitionRef
  definitionPath : String
  threadLocal : Bool
  initializer : Option AllocationMemory
  deriving BEq

structure VtablePredicate where
  kind : VtablePredicateKind
  definitionId : DefinitionRef
  definitionPath : Option String
  genericArgs : Array Miri.MIR.GenericArg
  boundVariables : Array Miri.MIR.BoundVariableKind
  projectionTerm : Option TypeId
  deriving BEq

structure VtableEntry where
  kind : VtableEntryKind
  instanceId : Option InstanceId
  allocationId : Option AllocationId
  traitDefinitionId : Option DefinitionRef
  traitDefinitionPath : Option String
  deriving BEq

structure VtableAllocation where
  principalPredicate : Option PredicateId
  typeId : TypeId
  sizeBytes : Option Nat
  alignBytes : Option Nat
  predicates : Array PredicateId
  entries : Array VtableEntry
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

structure SourceAllocIdSaltResult where
  salt : Nat
  allocationId : AllocationId
  sourceAllocId : UInt64
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


inductive CallResolutionKind where
  | direct | virtualDispatch | indirect | llvmIntrinsic
  deriving Repr, DecidableEq

/-- Only the compiler's LLVM intrinsic dispatch has no ordinary FnAbi. -/
inductive CallAbiEvidence where
  | normal (id : FunctionAbiId)
  | llvmIntrinsic
  deriving Repr, DecidableEq

structure CallResolutionEvidence where
  kind : CallResolutionKind
  instanceId : Option InstanceId
  functionType : Option TypeId
  dispatchSlot : Option Nat
  abi : CallAbiEvidence

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
  filename : Nat
  deriving Repr, DecidableEq

-- Hygiene collapse depends on the executable body, so this position is not the global span lo.
structure BacktraceSpan where
  spanId : SpanId
  position : CompilerSourcePosition
  deriving Repr, DecidableEq


structure LocalDecl where
  id : LocalId
  typeId : TypeId
  sourceInfo : SourceInfo

structure ThreadLocalEvidence where
  definition : DefinitionRef
  info : StaticGlobalInfo
  initializer : Option AllocationMemory

structure PlaceFact where
  place : Miri.MIR.Place
  typeId : TypeId
  projectionTypes : Array TypeId

structure DynamicUpcastEvidence where
  operandType : TypeId
  castTarget : TypeId
  sourceType : TypeId
  targetType : TypeId
  sourcePointeeType : TypeId
  targetPointeeType : TypeId
  sourceTailType : TypeId
  targetTailType : TypeId
  querySource : TypeId
  queryTarget : TypeId

structure NodeFacts where
  places : Array PlaceFact := #[]
  constantAllocations : Array AllocationId := #[]
  threadLocals : Array ThreadLocalEvidence := #[]
  dynamicUpcasts : Array DynamicUpcastEvidence := #[]

structure BodyCore where
  mir : Miri.MIR.Body
  definitionId : Option DefinitionRef
  defPath : String
  sourcePath : String
  spanId : SpanId
  preambleDefSpanId : SpanId
  injectionPhase : Option Miri.MIR.MirPhase
  instanceId : InstanceId
  localSources : Array SourceInfo
  sourceScopes : Array SourceScope
  backtraceSpans : Array BacktraceSpan
  callEvidence : Array (Option CallResolutionEvidence)
  nodeFacts : Array (Array NodeFacts)
  requiredConsts : Array Miri.MIR.ConstOperand

def BodyCore.threadLocals (body : BodyCore) : Array ThreadLocalEvidence :=
  (body.nodeFacts.map fun block => (block.map (·.threadLocals)).flatten).flatten

structure PromotedBody where
  index : Nat
  bodyId : Option BodyId

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

structure InstanceNode where
  instanceKind : Miri.Interpreter.CallInstanceKind
  genericArgs : Array Miri.MIR.GenericArg
  id : InstanceId
  kind : InstanceKind
  defPath : Option String
  definitionId : Option DefinitionRef
  bodyId : Option BodyId
  promotedBodies : Array PromotedBody
  dispatchSlot : Option Nat := none
  bodyStatus : Option String := none
  virtualIdentity : Option (TypeId × FunctionAbiId) := none
  foreignItem : Option Bool := none
  symbolName : Option String := none
  fallbackInstance : Option InstanceId := none

structure ScopeRoot where
  defPath : String
  definitionId : DefinitionRef
  deriving Repr, DecidableEq

structure SelectedScope where
  kind : String
  semantics : String
  roots : Array ScopeRoot

/-- Compiler-query target layout evidence, retained independently of a runtime
layout validator. Missing evidence is not inferred from the target triple. -/
structure TargetPointerSpec where
  pointerSizeBytes : Nat
  pointerAlignBytes : Nat
  pointerOffsetBytes : Nat
  isFat : Bool
  deriving Repr, DecidableEq

structure TargetAddressSpace where
  addressSpace : Nat
  spec : TargetPointerSpec
  objectSizeBoundBytes : Option Nat
  deriving Repr, DecidableEq

structure TargetDataLayoutEvidence where
  evidencePath : String
  llvmDataLayout : String
  privateInventoryEvidence : String
  alignmentEvidence : String
  endian : String
  pointerWidthBits : Nat
  objectSizeBoundBytes : Option Nat
  i1AlignBytes : Nat
  i8AlignBytes : Nat
  i16AlignBytes : Nat
  i32AlignBytes : Nat
  i64AlignBytes : Nat
  i128AlignBytes : Nat
  f16AlignBytes : Nat
  f32AlignBytes : Nat
  f64AlignBytes : Nat
  f128AlignBytes : Nat
  aggregateAlignBytes : Nat
  vectorAlign : Array (Nat × Nat)
  defaultAddressSpace : Nat
  defaultAddressSpacePointerSpec : TargetPointerSpec
  addressSpaceInfo : Array TargetAddressSpace
  instructionAddressSpace : Nat
  cEnumMinSize : String
  deriving Repr, DecidableEq

/-- Exact compiler existential-predicate identity, stable comparison rank and
late-bound-region-erasing normalization result under an explicit environment. -/
structure CompilerPredicateEvidence where
  id : Nat
  typingEnvironment : String
  stableKey : Nat
  autoTrait : Bool
  normalizedId : Option Nat
  original : PredicateId
  deriving BEq


end Miri.Input
