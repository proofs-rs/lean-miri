import Miri.Input.Model.Types
import Miri.MIR.SyntaxTables
import Miri.Interpreter.Instance
import Miri.ABI.ExternAbi
import Miri.Input.CompilerForeignData

namespace Miri.Input

/-- Compiler-selected type identities decoded once at the transport boundary.
Failures remain local to the queried entry, including unused unsupported queries. -/
structure CompilerTypeCatalogs where
  primitives : Except String (Array (String × Except String TypeId)) := .error "compiler runtime primitives absent"
  primitiveQueries : Except String (Array (String × Except String TypeId)) := .error "compiler runtime primitives absent"
  named : Except String (Array (String × Except String TypeId)) := .error "compiler named types absent"
  libc : Except String (Array (String × Except String TypeId)) := .error "compiler libc type layouts absent"
  windows : Except String (Array (String × Except String TypeId)) := .error "compiler Windows type layouts absent"
  deriving Repr, DecidableEq

namespace CompilerTypeCatalogs
def lookup (entries : Except String (Array (String × Except String TypeId))) (key : String) : Except String TypeId := do
  let entries ← entries
  let some (_,value) := entries.find? (·.1 == key) | throw s!"compiler type query absent: {key}"
  value
end CompilerTypeCatalogs

structure CompilerTables where
  spans : Array SourceSpanData := #[]
  definitions : Array DefinitionId := #[]
  typeConstants : Array MIR.TypeConst := #[]
  deriving Repr, DecidableEq

structure FunctionTypeData where
  definition : MIR.DefId
  args : Array MIR.GenericArg
  deriving Repr, DecidableEq

structure FunctionQueryData where
  kind : Miri.Interpreter.CallFunctionKind
  signature : Except String (Nat × ABI.ExternAbi)
  deriving Repr, DecidableEq

structure IntrinsicData where
  mustOverride : Bool
  fallbackIsSpec : Bool
  deriving Repr, DecidableEq

structure RuntimeInstanceData where
  instanceId : InstanceId
  display : String
  callerLocation : Bool
  inlineNever : Bool
  itemName : Except String String
  intrinsic : Except String (Option IntrinsicData)
  foreignItem : Bool
  closureLike : Bool
  symbolName : Except String String
  codegenSymbolName : Except String (Option String)
  targetFeatures : Except String (Array (String × Bool))
  deriving Repr, DecidableEq

structure RuntimeTypeData where
  pointerType : TypeId
  referenceType : TypeId
  dropGlue : Except String InstanceId
  deriving Repr, DecidableEq

structure RuntimeVirtualData where
  original : InstanceId
  methodDefinition : MIR.DefId
  parentTrait : MIR.DefId
  concreteType : TypeId
  rebasedArgs : Array MIR.GenericArg
  resolved : Except String InstanceId
  deriving Repr, DecidableEq

structure NativeSignatureData where
  instanceId : InstanceId
  signature : Except String (Array TypeId × TypeId)
  deriving Repr, DecidableEq

inductive PatternData where
  | range (start finish : MIR.TypeConstId)
  | or (children : Array Nat)
  | notNull
  deriving Repr, DecidableEq

structure NormalizationData where
  places : MIR.SharedTable MIR.TyId
  constants : Array (MIR.ConstantId × MIR.ConstantId)
  deriving Repr, DecidableEq

structure SourceScopeData where
  inlined : Option (Miri.Interpreter.CallInstance × MIR.SpanRef)
  parent : Option Nat
  trackCaller : Option Bool
  deriving Repr, DecidableEq

inductive RequiredConstantFailure where
  | invalidProgram (reason : String)
  | unsupported (reason : String)
  deriving Repr, DecidableEq

structure RequiredConstantCheck where
  source : MIR.ConstantId
  normalized : MIR.ConstantId
  value : MIR.ConstValue
  deriving Repr, DecidableEq

structure CallSiteData where
  status : Except String String
  kind : Except String String
  instanceId : Except String InstanceId
  dispatchSlot : Except String Nat
  functionType : Except String TypeId
  deriving Repr, DecidableEq

structure BacktracePositionData where
  bytePosition : UInt32
  line : Nat
  column : Nat
  filename : String
  deriving Repr, DecidableEq

structure BacktraceSpanData where
  span : MIR.SpanRef
  position : BacktracePositionData
  deriving Repr, DecidableEq

structure BodySourceData where
  callee : Except String Miri.Interpreter.CallInstance
  scopes : Array (Except String SourceScopeData)
  requiredConstants : Except String (Array (Except RequiredConstantFailure RequiredConstantCheck)) :=
    .error "required-constant compiler metadata absent"
  calls : Array (Except String (Option CallSiteData)) := #[]
  backtraceSpans : Except String (Array BacktraceSpanData) := .error "compiler backtrace span queries absent"
  deriving Repr, DecidableEq

structure SessionMetadataData where
  internalTargetFeatures : Except String (Array String)
  isLikeWasm : Except String Bool
  runtimeChecks : Except String (Array (MIR.RuntimeChecks × Bool)) := .error "compiler runtime checks absent"
  targetArch : Except String String := .error "compiler target architecture absent"
  deriving Repr, DecidableEq

structure RetagAttributeTable where
  entries : Array (DefinitionId × Except String Bool)
  absent : Except String Bool
  deriving Repr, DecidableEq

structure ThreadLocalStaticInfo where
  status : PayloadStatus
  sizeBytes : Nat
  alignBytes : Nat
  mutability : MemoryMutability
  isStatic : Bool
  foreignItem : Bool
  threadLocal : Bool
  nested : Except String Bool
  deriving Repr, DecidableEq

structure ThreadLocalQueryData where
  definition : MIR.DefId
  sourceDefinition : DefinitionId
  info : ThreadLocalStaticInfo
  initializer : Option AllocationMemory
  deriving Repr, DecidableEq

structure ThreadLocalTable where
  entries : MIR.SharedTable (Except String ThreadLocalQueryData)
  all : Except String (Array ThreadLocalQueryData)
  deriving Repr, DecidableEq

structure AllocationFunctionData where
  instanceId : InstanceId
  definitionId : DefinitionId
  callee : Miri.Interpreter.CallInstance
  deriving Repr, DecidableEq

structure FrameMetadataData where
  localCrate : Nat
  crates : Array (Nat × String)
  deriving Repr, DecidableEq

inductive CompilerGenericParameter where
  | lifetime | typeParameter | constParameter
  deriving Repr, DecidableEq

structure PanicQueryData where
  langItem : String
  definition : Except String (Option MIR.DefId)
  genericParameters : Except String (Array CompilerGenericParameter)
  deriving Repr, DecidableEq

structure NamedGlobalValueData where
  definition : MIR.DefId
  ty : MIR.TyId
  allocation : Nat
  isStatic : Bool
  deriving Repr, DecidableEq

structure NamedGlobalQueryData where
  name : String
  result : Except String NamedGlobalValueData
  deriving Repr, DecidableEq

structure NamedConstantValueData where
  sourceInstance : Miri.Interpreter.CallInstance
  ty : MIR.TyId
  value : MIR.ConstValue
  deriving Repr, DecidableEq

structure NamedConstantQueryData where
  name : String
  path : Except String (Array String)
  result : Except String NamedConstantValueData
  deriving Repr, DecidableEq

structure MainSignatureData where
  hasBoundVariables : Bool
  outputHasBoundVariables : Bool
  returnType : MIR.TyId
  fnPointerType : MIR.TyId
  deriving Repr, DecidableEq

structure MainEntryData where
  definition : MIR.DefId
  parameters : Array CompilerGenericParameter
  signature : Except String MainSignatureData
  start : Except String (Option Miri.Interpreter.CallInstance)
  deriving Repr, DecidableEq

structure LinkSectionData where
  definition : MIR.DefId
  span : MIR.SpanRef
  ty : MIR.TyId
  allocation : Nat
  deriving Repr, DecidableEq

structure LinkSectionQueryData where
  name : String
  result : Except String LinkSectionData
  deriving Repr, DecidableEq

structure MainQueryData where
  start : Option MIR.DefId
  compilerEntry : Option MIR.DefId
  compilerEntryType : Except String (Option (MIR.DefId × UInt8))
  entries : Array MainEntryData
  sections : Except String (Array LinkSectionQueryData)
  deriving Repr, DecidableEq

structure GlobalByteCandidateData where
  bytes : Array UInt8
  salts : Array (Option Nat)
  deriving Repr, DecidableEq

structure GlobalByteLegacyData where
  coveredAllocationIds : Array Nat
  candidates : Array GlobalByteCandidateData
  deriving Repr, DecidableEq

structure GlobalByteQueryData where
  legacy : Except String GlobalByteLegacyData
  strType : Except String MIR.TyId
  deriving Repr, DecidableEq

structure TypeNameConstantData where
  inputType : Option MIR.TyId
  sourceKey : Nat
  result : Except String (MIR.TyId × MIR.ConstValue)
  deriving Repr, DecidableEq

structure CallerLocationConstantData where
  span : Except String SourceSpanData
  sourceKey : Nat
  result : Except String (MIR.TyId × MIR.ConstValue)
  deriving Repr, DecidableEq

/-- Cast compiler evidence decoded at the transport boundary. Query failures
remain local until the interpreter requests that exact evidence. -/
inductive CastQueryValue where
  | resolved (instanceId : Option InstanceId)
  | tails (source target : TypeId)
  | boxType (typeId : TypeId)
  | supertraitSlot (slot : Option Nat)
  deriving Repr, DecidableEq

structure CastQueryData where
  identity : Nat
  kind : Except String String
  inputType : Except String TypeId
  inputSource : Except String TypeId
  inputTarget : Except String TypeId
  environment : Except String Unit
  noBoundVars : Except String Bool
  value : Except String CastQueryValue
  deriving Repr, DecidableEq

structure StartupQueryData where
  noCore : Except String Bool
  coreEscapeDefault : Except String (DefinitionId × Bool)
  deriving Repr, DecidableEq

structure MIRInputTables where
  castQueries : Except String (Array CastQueryData) := .error "compiler cast queries absent"
  mir : MIR.SyntaxTables := {}
  compiler : CompilerTables := {}
  bodies : Array MIR.BodyId := #[]
  normalizedBodies : Array (Except String MIR.BodyId) := #[]
  normalization : Array (Except String NormalizationData) := #[]
  instances : Array (Except String Miri.Interpreter.CallInstance) := #[]
  functionTypes : Array (Except String (Option FunctionTypeData)) := #[]
  functions : Array (Option FunctionQueryData) := #[]
  runtimeInstances : Except String (Array RuntimeInstanceData) := .ok #[]
  runtimeTypes : Except String (Array (Option RuntimeTypeData)) := .ok #[]
  runtimeVirtual : Except String (Array RuntimeVirtualData) := .ok #[]
  nativeSignatures : Except String (Array NativeSignatureData) := .ok #[]
  bodySources : Array BodySourceData := #[]
  patterns : Array PatternData := #[]
  patternIds : Array (Option Nat) := #[]
  sessionMetadata : Except String SessionMetadataData := .error "compiler session metadata absent"
  frameMetadata : Except String FrameMetadataData := .error "compiler frame metadata absent"
  panicQueries : Option (Except String (Array PanicQueryData)) := none
  namedGlobals : Except String (Array NamedGlobalQueryData) := .error "compiler named globals absent"
  foreignSymbols : Except String ForeignSymbolsData := .error "compiler foreign symbols absent"
  externStatics : Except String ExternStaticsData := .error "compiler extern statics absent"
  retagAttributes : Except String RetagAttributeTable := .error "compiler retag attributes absent"
  threadLocals : ThreadLocalTable := ⟨#[],.ok #[]⟩
  allocationFunctions : MIR.SharedTable (Except String AllocationFunctionData) := #[]
  namedConstants : Except String (Array NamedConstantQueryData) := .error "compiler named constants absent"
  mainQueries : Except String MainQueryData := .error "compiler main queries absent"
  globalByteQueries : Except String GlobalByteQueryData := .error "compiler global byte queries absent"
  typeNameConstants : Except String (Array TypeNameConstantData) := .error "compiler type-name constants absent"
  callerLocationConstants : Except String (Array CallerLocationConstantData) := .error "compiler caller-location constants absent"
  startupQueries : Except String StartupQueryData := .error "compiler startup queries absent"
  panicUnwinds : Except String Bool := .error "source compiler panic strategy is missing"
  deriving Repr, DecidableEq

def MIRInputTables.bodyId (tables : MIRInputTables) (index : Nat) : Except String MIR.BodyId :=
  match tables.bodies[index]? with
  | some id => pure id
  | none => throw s!"canonical MIR body {index} is absent"

def MIRInputTables.body (tables : MIRInputTables) (index : Nat) : Except String MIR.BodyNode := do
  let id ← tables.bodyId index
  (tables.mir.bodies.lookup id.index).mapError (fun id => s!"invalid MIR body ID {id}")

def MIRInputTables.normalizedBody (tables : MIRInputTables) (index : Nat) : Except String MIR.BodyNode := do
  let some result := tables.normalizedBodies[index]? | throw s!"normalized MIR body {index} is absent"
  let id ← result
  (tables.mir.bodies.lookup id.index).mapError (fun id => s!"invalid normalized MIR body ID {id}")

def MIRInputTables.instance (tables : MIRInputTables) (id : InstanceId) :
    Except String Miri.Interpreter.CallInstance := do
  let some result := tables.instances[id]? | throw s!"invalid instance ID {id}"
  result

def MIRInputTables.functionType (tables : MIRInputTables) (id : TypeId) : Except String FunctionTypeData := do
  let some result := tables.functionTypes[id]? | throw s!"invalid function type ID {id}"
  let some value ← result | throw s!"type {id} has no function/closure metadata"
  return value

end Miri.Input
