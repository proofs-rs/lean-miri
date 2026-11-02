import duplicate_prefix.S05PriorCellProgram
import Miri.Input.EvalPreparation
import Miri.Input.CompilerGlobalBytes
import Lean.Elab.Deriving.ToExpr
import Init.Internal.Order.While
attribute [local cbv_eval] Lean.Loop.forIn_eq_of_monadTail

/-! Reflection of the actual compiler preparation products. This is a data
preparation trust boundary like import_mir, never a safety theorem. Dependent
cache certificates are rebuilt by their public constructors. Optional caches
use their documented uncached representations. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 4096

open Lean Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory

namespace DuplicatePrefix.PriorCellMetadata

open Lean Elab Command in
private partial def deriveDataQuote (name : Name) : StateT NameSet CommandElabM Unit := do
  if (← get).contains name then return
  modify (·.insert name)
  let env ← getEnv
  let some info := env.find? name | return
  if !name.toString.startsWith "Miri." then return
  let custom := #[``LowerContext, ``RuntimeMetadata, ``RuntimeMetadata.Indexed,
    ``CompilerFacts.Context, ``CompilerInstanceAbi.Prepared, ``CompilerProviders.Prepared,
    ``EvalPreparation.Prepared, ``AllocationImage.Imported]
  if custom.contains name then return
  match info with
  | .inductInfo indInfo =>
    let found ← liftM <| liftTermElabM <| Meta.forallTelescopeReducing indInfo.type fun xs _ => do
      let type := mkAppN (mkConst name (indInfo.levelParams.map Level.param)) xs
      let classType ← Meta.mkAppM ``ToExpr #[type]
      Meta.synthInstance? classType
    if found.isSome then return
    for ctor in indInfo.ctors do
      let ctorInfo ← getConstInfo ctor
      for dependency in ctorInfo.type.getUsedConstants do
        if dependency != name then deriveDataQuote dependency
    liftM <| elabCommand (← `(deriving instance ToExpr for $(mkIdent name)))
  | .defnInfo definition =>
    let isTypeFormer ← liftM <| liftTermElabM <| Meta.forallTelescopeReducing definition.type fun _ body => do
      pure body.isSort
    if isTypeFormer then
      for dependency in definition.value.getUsedConstants do
        if dependency != name then deriveDataQuote dependency
  | _ => pure ()

open Lean Elab Command in
elab "derive_prior_cell_data_quote " names:ident,* : command => do
  let resolvedNames ← names.getElems.mapM fun name => resolveGlobalConstNoOverload name.raw
  let action : StateT NameSet CommandElabM Unit := do
    resolvedNames.forM deriveDataQuote
  discard <| action.run {}

deriving instance ToExpr for Except

section
variable [ToExpr Json]

derive_prior_cell_data_quote ImportDocument

/-- Diagnostic imports use the public uncached core projection. Reject a native
cached core rather than discarding its certificates during reflection. -/
instance : ToExpr ImportDocumentCore where
  toTypeExpr := mkConst ``ImportDocumentCore
  toExpr value :=
    if value.compilerFunctionAbiTable.isSome || value.compilerValueMemo.isSome then
      panic! "reflection requires a diagnostic uncached import core"
    else
      mkApp (mkConst ``ImportDocument.toCore)
        (toExpr (value.withTypedTree (.scalar .null)))

derive_prior_cell_data_quote LoweredProgram, RuntimeTargetDataLayout, RuntimeMetadataError, TyAndLayout

private def uncachedLowerContext (typeIds : Array TypeId)
    (scalarSizes : Array (TypeId × Nat)) (allocationIds : Array AllocationId)
    (obligations : Array Obligation) (sourceDocument : Option Json) : LowerContext :=
  {typeIds, scalarSizes, allocationIds, obligations, sourceDocument}

private def uncachedRuntime (source : ImportDocumentCore) (target : RuntimeTargetDataLayout)
    (layouts : Array (TypeId × Except RuntimeMetadataError (TyAndLayout TypeId))) : RuntimeMetadata :=
  {source, target, layouts}

private def uncachedFacts (runtime : RuntimeMetadata.Indexed) (program : LoweredProgram) : CompilerFacts.Context :=
  {runtime, program}

private def uncachedInstanceAbi (program : LoweredProgram)
    (entries : Array CompilerInstanceAbi.Entry) : CompilerInstanceAbi.Prepared :=
  {program, entries}


instance [ToExpr ImportDocumentCore] : ToExpr RuntimeMetadata where
  toTypeExpr := mkConst ``RuntimeMetadata
  toExpr value := mkApp3 (mkConst ``uncachedRuntime) (toExpr value.source)
    (toExpr value.target) (toExpr value.layouts)

instance [ToExpr RuntimeMetadata] : ToExpr RuntimeMetadata.Indexed where
  toTypeExpr := mkConst ``RuntimeMetadata.Indexed
  toExpr value :=
    let runtime := toExpr value.toRuntimeMetadata
    let raw := mkApp (mkConst ``ImportDocumentCore.raw) (mkApp (mkConst ``RuntimeMetadata.source) runtime)
    mkApp2 (mkConst ``RuntimeMetadata.Indexed.ofMetadata) runtime
      (mkApp (mkConst ``Option.none [0]) (mkApp (mkConst ``RuntimeMetadata.JsonReflexivity) raw))

instance [ToExpr RuntimeMetadata.Indexed] [ToExpr LoweredProgram] : ToExpr CompilerFacts.Context where
  toTypeExpr := mkConst ``CompilerFacts.Context
  toExpr value := mkApp2 (mkConst ``uncachedFacts) (toExpr value.runtime) (toExpr value.program)

instance {left : Json} : ToExpr (RuntimeMetadata.JsonReflexivity left) where
  toTypeExpr := mkApp (mkConst ``RuntimeMetadata.JsonReflexivity) (toExpr left)
  toExpr _ := mkApp (mkConst ``RuntimeMetadata.JsonReflexivity.prepare) (toExpr left)

instance [ToExpr RuntimeMetadata] {runtime : RuntimeMetadata} : ToExpr (CallResolution.FunctionAbiCache runtime) where
  toTypeExpr := mkApp (mkConst ``CallResolution.FunctionAbiCache) (toExpr runtime)
  toExpr _ := mkApp (mkConst ``CallResolution.prepareFunctionAbiCache) (toExpr runtime)

instance [ToExpr RuntimeMetadata] {runtime : RuntimeMetadata} : ToExpr (CallCompatibility.UnitLayoutCache runtime) where
  toTypeExpr := mkApp (mkConst ``CallCompatibility.UnitLayoutCache) (toExpr runtime)
  toExpr _ := mkApp (mkConst ``CallCompatibility.bindUnitLayout) (toExpr runtime)

section
variable [ToExpr LoweredProgram] [ToExpr RuntimeMetadata]

derive_prior_cell_data_quote CompilerInstanceAbi.Entry

instance : ToExpr CompilerInstanceAbi.Prepared where
  toTypeExpr := mkConst ``CompilerInstanceAbi.Prepared
  toExpr value := mkApp2 (mkConst ``uncachedInstanceAbi) (toExpr value.program) (toExpr value.entries)

derive_prior_cell_data_quote CompilerLifecyclePipeline.Prepared, CompilerFunctionFacts.Prepared,
  CompilerMain.Prepared, CompilerIntrinsicFacts.Prepared, CompilerConstantQueries.Prepared,
  CompilerNamedConstants.Prepared, CompilerNamedGlobals.Prepared, CompilerExternStatic.Prepared,
  CompilerFunctionPointers.Prepared, CompilerVTableMachine.Prepared, CompilerNamedShimAbi.Prepared,
  CompilerForeignSymbolTables.Prepared, RuntimeArrayTypes.World, CompilerThreadLocal.Entry,
  EvalEntryMachine.Layouts, CompilerGlobalBytes.Prepared


@[noinline] private def checkedVector {α : Type u} (length : Nat) (items : Array α)
    (size : items.size = length) : Vector α length := ⟨items, size⟩

instance {α : Type u} [ToLevel.{u}] [ToExpr α] {length : Nat} : ToExpr (Vector α length) where
  toTypeExpr := mkApp2 (mkConst ``Vector [toLevel.{u}]) (toTypeExpr α) (toExpr length)
  toExpr value := mkApp4 (mkConst ``checkedVector [toLevel.{u}]) (toTypeExpr α)
    (toExpr length) (toExpr value.toArray)
    (mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Nat) (toExpr length))

derive_prior_cell_data_quote Allocation

instance : ToExpr AllocationImage.Imported where
  toTypeExpr := mkConst ``AllocationImage.Imported
  toExpr value := mkApp2 (mkConst ``AllocationImage.Imported.ofSource)
    (toExpr value.source) (toExpr value.initializers)

private def rebuildProviders (program : LoweredProgram) (runtime : RuntimeMetadata)
    (lifecycle : CompilerLifecyclePipeline.Prepared) (functions : CompilerFunctionFacts.Prepared)
    (main : CompilerMain.Prepared) (intrinsics : CompilerIntrinsicFacts.Prepared)
    (constants : CompilerConstantQueries.Prepared) (namedConstants : CompilerNamedConstants.Prepared)
    (namedGlobals : CompilerNamedGlobals.Prepared) (externStatics : CompilerExternStatic.Prepared)
    (pointers : CompilerFunctionPointers.Prepared) (vtables : CompilerVTableMachine.Prepared)
    (namedAbi : CompilerNamedShimAbi.Prepared)
    (foreignSymbols : Except String CompilerForeignSymbolTables.Prepared)
    (initialArrays : Except String RuntimeArrayTypes.World)
    (tls : Except String (Array CompilerThreadLocal.Entry)) : CompilerProviders.Prepared :=
  let sourceEquality := RuntimeMetadata.JsonReflexivity.prepare (left := runtime.source.raw)
  { program, runtime, lifecycle, functions, main, intrinsics, constants,
    sourceEquality, constantBinding := CompilerConstantQueries.bind constants runtime (some sourceEquality),
    namedConstants, namedGlobals, externStatics, pointers, vtables, namedAbi, foreignSymbols,
    covarianceIndex := CompilerQueryIndices.covariance program.input.raw,
    signatureAbiIndex := CompilerQueryIndices.signatureAbi runtime program.input.raw,
    initialArrays, tls }

instance : ToExpr CompilerProviders.Prepared where
  toTypeExpr := mkConst ``CompilerProviders.Prepared
  toExpr value := mkAppN (mkConst ``rebuildProviders) #[
    toExpr value.program, toExpr value.runtime, toExpr value.lifecycle,
    toExpr value.functions, toExpr value.main, toExpr value.intrinsics,
    toExpr value.constants, toExpr value.namedConstants, toExpr value.namedGlobals,
    toExpr value.externStatics, toExpr value.pointers, toExpr value.vtables,
    toExpr value.namedAbi, toExpr value.foreignSymbols, toExpr value.initialArrays,
    toExpr value.tls]

instance : ToExpr EvalPreparation.Prepared where
  toTypeExpr := mkConst ``EvalPreparation.Prepared
  toExpr value := mkAppN (mkConst ``EvalPreparation.Prepared.mk) #[
    toExpr value.compiler, toExpr value.image, toExpr value.types,
    toExpr value.layouts, toExpr value.dummySpan]

end
end



/-- The actual preparation profile has no materialized local allocation. All
compiler registration tables and identity-supply fields are retained as data;
only their certified lookup indexes are rebuilt by public setters. -/
structure InitialMemoryData where
  nextAllocId : UInt64
  idSupplyExhausted : Bool
  issuedIds : Array AllocId
  dead : Array DeadAllocation
  globals : Array GlobalAllocation
  importedGlobalIds : Array (Nat × AllocId)
  extraFnPtrIds : Array AllocId
  vaListIds : Array AllocId
  byteGlobalKeys : Array (Array UInt8 × Fin 32 × AllocId)
  byteGlobalKeysReady : Bool
  sourceAllocIdWorldActive : Bool
  sourceAllocIdNext : UInt64
  sourceAllocIdExhausted : Bool
  sourceAllocIdByRuntime : Array (AllocId × UInt64)
  runtimeBySourceAllocId : Array (UInt64 × AllocId)
  opaqueSourceGlobalIds : Array UInt64
  sourceByteImageFamilyComplete : Bool

section
variable [ToExpr Json]
derive_prior_cell_data_quote DeadAllocation, GlobalAllocation

deriving instance ToExpr for InitialMemoryData
end

def InitialMemoryData.restore (data : InitialMemoryData) :
    MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind :=
  let memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind := {
    nextAllocId := data.nextAllocId, idSupplyExhausted := data.idSupplyExhausted,
    live := #[], dead := data.dead,
    byteGlobalKeys := data.byteGlobalKeys, byteGlobalKeysReady := data.byteGlobalKeysReady,
    sourceAllocIdWorldActive := data.sourceAllocIdWorldActive,
    sourceAllocIdNext := data.sourceAllocIdNext, sourceAllocIdExhausted := data.sourceAllocIdExhausted,
    opaqueSourceGlobalIds := data.opaqueSourceGlobalIds,
    sourceByteImageFamilyComplete := data.sourceByteImageFamilyComplete }
  let memory := memory.setIssuedIds data.issuedIds
  let memory := memory.setGlobalEntries data.globals
  let memory := memory.setImportedGlobalIds data.importedGlobalIds
  let memory := memory.setExtraFunctionIds data.extraFnPtrIds
  let memory := memory.setVaListIds data.vaListIds
  memory.setSourceAllocIdCrosswalks data.sourceAllocIdByRuntime data.runtimeBySourceAllocId

private def captureInitialMemory
    (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind) :
    Except String InitialMemoryData := do
  unless memory.live.isEmpty do throw "initial preparation has materialized allocations; zero-live serializer is inapplicable"
  return {
    nextAllocId := memory.nextAllocId, idSupplyExhausted := memory.idSupplyExhausted,
    issuedIds := memory.issuedIds, dead := memory.dead, globals := memory.globals,
    importedGlobalIds := memory.importedGlobalIds, extraFnPtrIds := memory.extraFnPtrIds,
    vaListIds := memory.vaListIds, byteGlobalKeys := memory.byteGlobalKeys,
    byteGlobalKeysReady := memory.byteGlobalKeysReady,
    sourceAllocIdWorldActive := memory.sourceAllocIdWorldActive,
    sourceAllocIdNext := memory.sourceAllocIdNext, sourceAllocIdExhausted := memory.sourceAllocIdExhausted,
    sourceAllocIdByRuntime := memory.sourceAllocIdByRuntime,
    runtimeBySourceAllocId := memory.runtimeBySourceAllocId,
    opaqueSourceGlobalIds := memory.opaqueSourceGlobalIds,
    sourceByteImageFamilyComplete := memory.sourceByteImageFamilyComplete }

private structure ReflectionSource where
  document : ImportDocument
  prepared : EvalPreparation.Prepared
  bytes : CompilerGlobalBytes.Prepared
  memory : InitialMemoryData

private def readPreparation (path : String) : IO (Except String ReflectionSource) := do
  let decoded ← Input.decodeFile path
  return do
    let decoded ← decoded
    let lowered ← lowerProgram decoded.document
    let attempted := EvalPreparation.prepare lowered
    let prepared ← attempted.outcome
    let bytes ← CompilerGlobalBytes.prepare prepared.compiler.program prepared.compiler.runtime
      attempted.memory (some prepared.compiler.sourceEquality)
    let memory ← captureInitialMemory attempted.memory
    pure ⟨decoded.document, prepared, bytes, memory⟩

private def quoteProgram [ToExpr Json] [ToExpr ImportDocumentCore] (program : LoweredProgram) : Expr :=
  mkAppN (mkConst ``LoweredProgram.mk) #[toExpr program.bundle, toExpr program.roots,
    toExpr program.instances, toExpr program.promoted, toExpr program.input]

private def addData (name : Name) (type value : Expr) : MetaM Unit := do
  let declaration := Declaration.defnDecl {
    name, levelParams := [], type, value, hints := .regular 0, safety := .safe }
  addDecl declaration
  Meta.setInlineAttribute name .noinline
  compileDecl declaration

private structure SplitState where
  next : Nat := 0
  cache : Std.HashMap Expr (Expr × Nat) := {}

private partial def splitData (base : Name) (value : Expr) : StateT SplitState MetaM (Expr × Nat) := do
  if let some previous := (← get).cache[value]? then return previous
  let original := value
  let (value, size) ← match value with
    | .app fn arg => do
      let (fn, fnSize) ← splitData base fn
      let (arg, argSize) ← splitData base arg
      pure (mkApp fn arg, fnSize + argSize + 1)
    | _ => pure (value, 1)
  if size < 1024 then
    modify fun state => {state with cache := state.cache.insert original (value,size)}
    return (value,size)
  let type ← Meta.inferType value
  if type.isForall || (← Meta.isProp type) then
    modify fun state => {state with cache := state.cache.insert original (value,size)}
    return (value,size)
  let index := (← get).next
  modify fun state => {state with next := index + 1}
  let name := base ++ Name.mkSimple s!"_prepared_chunk_{index}"
  addData name type value
  let result := (mkConst name, 1)
  modify fun state => {state with cache := state.cache.insert original result}
  return result

private def emitData (name : Name) (type value : Expr) : MetaM Unit := do
  let (value, _) ← (splitData name value).run' {}
  addData name type value

syntax (name := reflectPreparation) "reflect_prior_cell_preparation " str " as " ident : command

open Lean Elab Command in
elab_rules : command
  | `(reflect_prior_cell_preparation $path:str as $base:ident) => do
    let source ← liftIO (readPreparation path.getString)
    let source ← match source with
      | .ok source => pure source
      | .error reason => throwErrorAt path "compiler preparation failed: {reason}"
    unless source.document.raw == DuplicatePrefix.PriorCellProgram.imported.document.raw do
      throwErrorAt path "preparation source differs from the imported fixed document"
    let base := (← getCurrNamespace) ++ base.getId
    liftTermElabM <| withOptions (Elab.async.set · false) do
      let env ← getEnv
      let mut shared : Std.HashMap Json Expr := {}
      for h : index in [:source.document.sharedNodes.size] do
        let name := ``DuplicatePrefix.PriorCellProgram.imported ++ Name.mkSimple s!"_mir_json_{index}"
        unless env.contains name do
          throwError "fixed document is missing shared JSON declaration {name}"
        shared := shared.insert source.document.sharedNodes[index] (mkConst name)
      let documentExpr := mkApp (mkConst ``DecodeResult.document) (mkConst ``DuplicatePrefix.PriorCellProgram.imported)
      shared := shared.insert source.document.raw (mkApp (mkConst ``ImportDocument.raw) documentExpr)
      let originalJson : ToExpr Json := inferInstance
      letI : ToExpr Json := {
        toTypeExpr := mkConst ``Json
        toExpr := fun value => match shared[value]? with
          | some expr => expr
          | none => originalJson.toExpr value }
      let originalCore : ToExpr ImportDocumentCore := inferInstance
      let sourceCore := originalCore.toExpr source.document.toCore
      let sourceExpr := mkApp (mkConst ``ImportDocument.toCore) documentExpr
      letI : ToExpr ImportDocumentCore := {
        toTypeExpr := mkConst ``ImportDocumentCore
        toExpr := fun value =>
          let quoted := originalCore.toExpr value
          if quoted == sourceCore then sourceExpr else quoted }
      let programName := base ++ `program
      let programValue := quoteProgram source.prepared.compiler.program
      letI : ToExpr LoweredProgram := {
        toTypeExpr := mkConst ``LoweredProgram
        toExpr := fun value =>
          let quoted := quoteProgram value
          if quoted == programValue then mkConst programName else quoted }
      let originalRuntime : ToExpr RuntimeMetadata := inferInstance
      let runtimeName := base ++ `runtime
      let runtimeValue := originalRuntime.toExpr source.prepared.compiler.runtime
      letI : ToExpr RuntimeMetadata := {
        toTypeExpr := mkConst ``RuntimeMetadata
        toExpr := fun value =>
          let quoted := originalRuntime.toExpr value
          if quoted == runtimeValue then mkConst runtimeName else quoted }
      let products : Array (Name × Expr × Expr) := #[
        (programName, mkConst ``LoweredProgram, programValue),
        (runtimeName, mkConst ``RuntimeMetadata, runtimeValue),
        (base ++ `compiler, mkConst ``CompilerProviders.Prepared, toExpr source.prepared.compiler),
        (base ++ `image, mkConst ``AllocationImage.Imported, toExpr source.prepared.image),
        (base ++ `types, mkConst ``RuntimeArrayTypes.World, toExpr source.prepared.types),
        (base ++ `layouts, mkConst ``EvalEntryMachine.Layouts, toExpr source.prepared.layouts),
        (base ++ `dummySpan, mkConst ``MIR.SpanRef, toExpr source.prepared.dummySpan),
        (base ++ `bytes, mkConst ``CompilerGlobalBytes.Prepared, toExpr source.bytes),
        (base ++ `memoryData, mkConst ``InitialMemoryData, toExpr source.memory)]
      for (name, type, value) in products do
        emitData name type value
      addData (base ++ `initialMemory)
        (mkAppN (mkConst ``MemoryState) #[mkConst ``Provenance, mkConst ``Miri.TreeBorrows.BorrowTree, mkConst ``MiriMemoryKind])
        (mkApp (mkConst ``InitialMemoryData.restore) (mkConst (base ++ `memoryData)))
      addData (base ++ `prepared) (mkConst ``EvalPreparation.Prepared)
        (mkAppN (mkConst ``EvalPreparation.Prepared.mk) #[mkConst (base ++ `compiler),
          mkConst (base ++ `image), mkConst (base ++ `types), mkConst (base ++ `layouts),
          mkConst (base ++ `dummySpan)])

reflect_prior_cell_preparation "examples/duplicate_prefix/prior_cell_context/input.json" as actual

end DuplicatePrefix.PriorCellMetadata
