import duplicate_prefix.S05PriorCellProgram
import duplicate_prefix.Reflection

/-! Kernel-checked reflection of typed compiler preparation products. The
preparation input is checked against the imported fixed document before quoting. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option synthInstance.maxSize 4096

open Lean Miri Miri.ABI Miri.Input Miri.Interpreter Miri.Memory

namespace DuplicatePrefix.PriorCellMetadata

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

derive_duplicate_prefix_quote DeadAllocation, GlobalAllocation

deriving instance ToExpr for InitialMemoryData

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
  layoutResults : Array (Except RuntimeMetadataError (TyAndLayout TypeId))
  abiResults : Array (Except String (FnAbi TypeId))

private def readPreparation (path : String) : IO (Except String ReflectionSource) := do
  let decoded ← Input.decodeFile path
  return do
    let decoded ← decoded
    let lowered ← lowerProgram decoded.document
    let attempted := EvalPreparation.prepare lowered
    let prepared ← attempted.outcome
    let bytes ← CompilerGlobalBytes.prepare prepared.compiler.program prepared.compiler.runtime
      attempted.memory
    let memory ← captureInitialMemory attempted.memory
    let layoutResults := prepared.compiler.runtime.source.types.map fun node =>
      prepared.compiler.runtime.lookup node.id
    let abiResults := prepared.compiler.program.input.functionAbis.map fun row =>
      CallResolution.functionAbi prepared.compiler.runtime row
    pure ⟨decoded.document, prepared, bytes, memory, layoutResults, abiResults⟩

private def quoteProgram [ToExpr ImportDocument] (program : LoweredProgram) : Expr :=
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
    let sourceMatches ← liftTermElabM <| Meta.isDefEq (toExpr source.document)
      (mkApp (mkConst ``ExecutionInput.document) (mkConst ``DuplicatePrefix.PriorCellProgram.imported))
    unless sourceMatches do
      throwErrorAt path "preparation source differs from the imported fixed document"
    let base := (← getCurrNamespace) ++ base.getId
    liftTermElabM <| withOptions (Elab.async.set · false) do
      let documentExpr := mkApp (mkConst ``ExecutionInput.document) (mkConst ``DuplicatePrefix.PriorCellProgram.imported)
      let originalDocument : ToExpr ImportDocument := inferInstance
      let sourceValue := originalDocument.toExpr source.document
      letI : ToExpr ImportDocument := {
        toTypeExpr := mkConst ``ImportDocument
        toExpr := fun value =>
          let quoted := originalDocument.toExpr value
          if quoted == sourceValue then documentExpr else quoted }
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
        (base ++ `memoryData, mkConst ``InitialMemoryData, toExpr source.memory),
        (base ++ `layoutResults, toTypeExpr (Array (Except RuntimeMetadataError (TyAndLayout TypeId))), toExpr source.layoutResults),
        (base ++ `abiResults, toTypeExpr (Array (Except String (FnAbi TypeId))), toExpr source.abiResults)]
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
