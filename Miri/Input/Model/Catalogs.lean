import Miri.Input.Model.Types
import Miri.MIR.Syntax
import Miri.ABI.ExternAbi

namespace Miri.Input.Catalog

structure Signature where
  inputs : Array TypeId
  output : TypeId
  safety : Miri.MIR.Safety
  abi : Miri.ABI.ExternAbi
  cVariadic : Bool
  deriving Repr, DecidableEq

structure Artifact where
  path : String
  sha256 : String
  sizeBytes : Nat
  crateName : String
  kind : String
  withinSysroot : Bool
  sysrootRelativePath : Option String
  deriving Repr, DecidableEq

structure ProducerSettings where
  sysrootPath : String
  hashAlgorithm : String
  sysrootManifestSha256 : String
  loadedArtifactsManifestSha256 : String
  artifacts : Array Artifact
  requestedCfgMiri : Bool
  miriDefaultArgs : Array String
  rustcArgs : Array String
  effectivePanicStrategy : String
  mirOptLevel : Option Nat
  mirEnablePasses : Array (String × Bool)
  mirPreserveUb : Bool
  extraConstUbChecks : Bool
  alwaysEncodeMir : Bool
  deduplicateDiagnostics : Bool
  qualification : String
  deriving Repr, DecidableEq

/-- Raw compiler/session print configuration, not a per-type formatting result. -/
structure PrintOptions where
  typeLengthLimit : Nat
  verboseInternals : Bool
  identifyRegions : Bool
  trimDiagnosticPaths : Bool := false
  trimmedDefPaths : Bool := false
  deriving Repr, DecidableEq

structure Session where
  internalTargetFeatures : Array String
  isLikeWasm : Bool
  targetArch : String
  rootSpan : SpanId
  runtimeChecks : Array (Miri.MIR.RuntimeChecks × Bool)
  printOptions : Option PrintOptions := none
  deriving Repr, DecidableEq

structure IntrinsicMetadata where
  mustOverride : Bool
  fallbackIsSpec : Bool
  deriving Repr, DecidableEq

structure TargetFeature where
  name : String
  kind : String
  deriving Repr, DecidableEq

structure RuntimeInstance where
  instanceId : InstanceId
  display : String
  inlineNever : Bool
  targetFeatures : Array TargetFeature
  isForeignItem : Bool
  isClosureLike : Bool
  intrinsicMetadata : Option (Option IntrinsicMetadata)
  itemName : Option String
  codegenSymbolName : Option (Option String)
  symbolName : Option String
  deriving Repr, DecidableEq

structure RuntimeType where
  inputType : TypeId
  dropGlue : Option InstanceId
  deriving Repr, DecidableEq

structure VtableRef where
  inputType : TypeId
  inputPredicates : Array PredicateId
  queryId : Nat
  deriving Repr, DecidableEq

structure RuntimeVirtual where
  originalInstance : InstanceId
  methodDefinition : DefinitionRef
  parentTrait : DefinitionRef
  concreteType : TypeId
  parentGenericCount : Nat
  resolved : InstanceId
  vtableQuery : VtableRef
  deriving Repr, DecidableEq

structure Startup where
  noCore : Bool
  coreEscapeDefault : Option (DefinitionRef × Bool)
  deriving Repr, DecidableEq

inductive ImportLinkage where
  | none
  | externalWeak (raw : String)
  | other (raw : String)
  deriving Repr, DecidableEq

structure ExternDeclaration where
  definition : DefinitionRef
  symbol : String
  typeId : TypeId
  layoutId : LayoutId
  importLinkage : ImportLinkage
  definitionMutability : MemoryMutability
  typeIsFreeze : Bool
  declIsMut : Bool
  deriving Repr, DecidableEq

structure ForeignCandidate where
  iterationIndex : Nat
  used : Bool
  symbol : String
  definition : DefinitionRef
  explicitSymbol : Bool
  crateIndex : Nat
  crateName : String
  weak : Bool
  span : SpanId
  definitionKind : String
  compilerBuiltins : Bool
  instanceId : Option InstanceId
  deriving Repr, DecidableEq

inductive SelectedExport where
  | ambiguous (symbol reason : String)
  | other (symbol kind : String) (definition : DefinitionRef) (instanceId : Option InstanceId)
  | static (symbol : String) (definition : DefinitionRef)
      (declaration : ExternDeclaration) (allocation : AllocationId)
  deriving Repr, DecidableEq

inductive ForeignFallback where
  | ambiguous (symbol reason : String)
  | candidate (value : ForeignCandidate)
  deriving Repr, DecidableEq

inductive AllocatorTarget where
  | special (method : String)
  | redirect (symbol : String)
  deriving Repr, DecidableEq

structure ForeignSymbols where
  os : String
  env : String
  binaryFormat : String
  families : Array String
  noAllocShimSymbol : String
  allocatorShims : Array (String × AllocatorTarget)
  exportedCandidates : Option (Array ForeignCandidate)
  selectedForeignFallbacks : Option (Array ForeignFallback)
  externDeclarations : Option (Array ExternDeclaration)
  selectedExports : Option (Array SelectedExport)
  deriving Repr, DecidableEq

structure Runtime where
  startup : Option Startup
  types : Array RuntimeType
  virtualQueries : Array RuntimeVirtual
  instances : Array RuntimeInstance
  foreignSymbols : ForeignSymbols
  deriving Repr, DecidableEq

structure FrameMetadata where
  localCrate : Nat
  crates : Array (Nat × String)
  deriving Repr, DecidableEq

structure InstanceAbi where
  instanceId : InstanceId
  extraArgumentTypes : Array TypeId
  abiId : FunctionAbiId
  deriving Repr, DecidableEq

structure FunctionType where
  typeId : TypeId
  instanceId : Option InstanceId
  signature : Signature
  deriving Repr, DecidableEq

structure PointerAbi where
  typeId : TypeId
  extraArgumentTypes : Array TypeId
  abiId : FunctionAbiId
  deriving Repr, DecidableEq

structure HelperSignature where
  signature : Signature
  splatted : Bool
  abiId : FunctionAbiId
  deriving Repr, DecidableEq

structure FunctionFacts where
  types : Array FunctionType
  pointerAbis : Array PointerAbi
  helperSignatures : Array HelperSignature
  deriving Repr, DecidableEq

inductive CastQuery where
  | resolveFnPtr (input : TypeId) (argsNoBoundVars : Bool) (instanceId : Option InstanceId)
  | resolveClosureFnOnce (input : TypeId) (argsNoBoundVars : Bool) (instanceId : InstanceId)
  | supertraitSlot (source target : TypeId) (slot : Option Nat)
  | lockstepTails (source target sourceTail targetTail : TypeId)
  | boxType (input output : TypeId)
  deriving Repr, DecidableEq

structure CallerLocation where
  span : SpanId
  resultType : Option TypeId
  value : Miri.MIR.ConstValue
  deriving Repr, DecidableEq

structure PanicQuery where
  langItem : String
  definition : Option DefinitionRef
  genericParameters : Option (Array String)
  deriving Repr, DecidableEq

structure NativeSignature where
  instanceId : InstanceId
  query : String
  normalization : String
  boundRegions : String
  signature : Signature
  deriving Repr, DecidableEq

structure RetagQuery where
  definition : DefinitionRef
  rustcNoWritable : Bool
  deriving Repr, DecidableEq

structure CovarianceQuery where
  sourceType : TypeId
  targetType : TypeId
  value : Bool
  deriving Repr, DecidableEq

structure GlobalByteCandidate where
  bytesHex : String
  salts : Array (Nat × Option AllocationId)
  deriving Repr, DecidableEq

structure GlobalBytes where
  saltCount : Nat
  strType : TypeId
  coveredAllocations : Array AllocationId
  candidates : Array GlobalByteCandidate
  deriving Repr, DecidableEq

structure StartResolution where
  instanceId : InstanceId
  functionType : TypeId
  deriving Repr, DecidableEq

structure EntrySignature where
  compilerSelectedEntry : Bool
  hasBoundVariables : Bool
  outputHasBoundVariables : Bool
  returnType : TypeId
  functionPointerType : TypeId
  startResolution : Option StartResolution
  deriving Repr, DecidableEq

structure MainEntry where
  definition : DefinitionRef
  genericParameters : Array String
  signature : EntrySignature
  deriving Repr, DecidableEq

structure CompilerEntry where
  definition : DefinitionRef
  kind : String
  sigpipe : Nat
  deriving Repr, DecidableEq

structure LinkSection where
  sectionName : String
  definition : DefinitionRef
  span : SpanId
  typeId : TypeId
  allocation : AllocationId
  deriving Repr, DecidableEq

structure Main where
  startLangItem : Option DefinitionRef
  compilerEntry : Option DefinitionRef
  compilerEntryType : Option CompilerEntry
  entries : Array MainEntry
  linkSections : Option (Array LinkSection)
  deriving Repr, DecidableEq

structure Primitives where
  u8 : TypeId
  u16 : TypeId
  u32 : TypeId
  u64 : TypeId
  u128 : TypeId
  i8 : TypeId
  i16 : TypeId
  i32 : TypeId
  i64 : TypeId
  i128 : TypeId
  bool : TypeId
  pointerTagInteger : TypeId
  usize : TypeId
  isize : TypeId
  unit : TypeId
  unitPointerConst : TypeId
  unitPointerMut : TypeId
  immU8Pointer : TypeId
  immU8PointerPointer : TypeId
  callerLocationType : Option TypeId
  orderingEnum : Option TypeId
  deriving Repr, DecidableEq

structure VtableQuery where
  queryId : Nat
  inputType : TypeId
  inputPredicates : Array PredicateId
  outputType : TypeId
  outputPredicates : Array PredicateId
  outputTypeMonomorphic : Bool
  outputPredicatesMonomorphic : Bool
  vtableAllocation : Option AllocationId
  metadata : VtableAllocation

structure ShimSignature where
  callingConvention : String
  arguments : Array String
  result : String
  cVariadic : Bool
  deriving Repr, DecidableEq

structure ShimAbi where
  signature : ShimSignature
  inputTypes : Array TypeId
  outputType : TypeId
  abiId : FunctionAbiId
  deriving Repr, DecidableEq

structure NamedShimAbi where
  name : String
  recipe : ShimAbi
  sourceTargetOpIsUlong : Option Bool
  deriving Repr, DecidableEq

structure TypeLayouts where
  cratePath : Array String
  namespaceName : String
  entries : Array (String × TypeId)
  deriving Repr, DecidableEq

structure NamedConstant where
  name : String
  path : Array String
  instanceId : InstanceId
  typeId : TypeId
  value : Miri.MIR.ConstValue
  deriving Repr, DecidableEq

structure NamedStatic where
  name : String
  path : Array String
  definition : DefinitionRef
  isStatic : Bool
  typeId : TypeId
  allocation : AllocationId
  deriving Repr, DecidableEq

abbrev ThreadLocal := ThreadLocalEvidence

structure Queries where
  session : Session
  runtime : Runtime
  frameMetadata : FrameMetadata
  instanceAbis : Array InstanceAbi
  functionFacts : FunctionFacts
  casts : Array CastQuery
  panic : Array PanicQuery
  nativeSignatures : Array NativeSignature
  retag : Array RetagQuery
  covariance : Array CovarianceQuery
  globalBytes : GlobalBytes
  callerLocations : Array CallerLocation
  main : Main
  primitives : Primitives
  vtables : Array VtableQuery
  namedTypes : Option (Array (String × TypeId))
  shimAbis : Option (Array ShimAbi)
  namedShimAbis : Option (Array NamedShimAbi)
  libcTypeLayouts : Option TypeLayouts
  windowsTypeLayouts : Option TypeLayouts
  namedConstants : Option (Array NamedConstant)
  namedStatics : Option (Array NamedStatic)

end Miri.Input.Catalog
