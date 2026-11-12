import Miri.Input.CompilerLinkSections

/-! Exact compiler support for `machine.rs::extern_static_pointer`.
Declaration metadata is keyed by shared DefId identity. Exported-static
resolution retains the source-selected symbol winner and its allocation ID;
the winner is materialized only through the canonical imported global table.
-/
namespace Miri.Input.CompilerExternStatic
open Lean Miri.ABI Miri.Memory Miri.Interpreter

structure Declaration where
  definition : MIR.DefId
  symbol : String
  size : Size
  align : Align
  linkage : ExternStatic.ImportLinkage
  mutable : Bool
  result : Except String Unit
  deriving DecidableEq, Repr

structure Winner where
  definition : Option MIR.DefId
  kind : String
  allocation : Option AllocationId
  result : Except StepError Unit

structure Selected where
  symbol : String
  winner : Winner

/-- Target attributes returned by rustc's parsed Session target. `families`
is the exact cfg family set; neither family nor environment is inferred from
the target triple. -/
structure TargetFacts where
  os : String
  env : String
  binaryFormat : String
  families : Array String
  deriving DecidableEq, Repr

structure Prepared where
  program : LoweredProgram
  runtime : RuntimeMetadata
  sourceResult : Except String Unit
  targetFacts : Except String TargetFacts
  declarations : Array Declaration
  selected : Array Selected

private def definition (tables : CompilerTables) (id : Nat) : Except String MIR.DefId := do
  unless id < tables.definitions.size do throw "compiler definition ID out of bounds"
  pure id

private def linkage : Catalog.ImportLinkage → ExternStatic.ImportLinkage
  | .none => .none | .externalWeak _ => .externalWeak | .other _ => .other

private def decodeDeclaration (runtime : RuntimeMetadata) (ctx : LowerContext) (tables : CompilerTables)
    (raw : Catalog.ExternDeclaration) : Except String Declaration := do
  let definitionId ← definition tables raw.definition
  let result := do
    unless ctx.containsTypeId raw.typeId do throw "extern-static declaration references absent compiler type"
    let some layout := ctx.layouts[raw.layoutId]? | throw "extern-static layout ID out of bounds"
    let computed ← RuntimeMetadata.layout runtime.target layout |>.mapError toString
    let size := computed.size
    let align := computed.align.abi
    let sourceMutability := raw.definitionMutability == MemoryMutability.mutable || !raw.typeIsFreeze
    unless raw.declIsMut == sourceMutability do
      throw "extern-static declaration mutability disagrees with definition mutability and Freeze query"
    pure (size, align)
  match result with
  | .ok (size, align) => pure ⟨definitionId, raw.symbol, size, align, linkage raw.importLinkage, raw.declIsMut, .ok ()⟩
  | .error reason => pure ⟨definitionId, raw.symbol, .ZERO, .ONE, .other, false, .error reason⟩

private def selectedWinner (runtime : RuntimeMetadata) (ctx : LowerContext) (tables : CompilerTables)
    (raw : Catalog.SelectedExport) : Except String (String × Winner) := do
  match raw with
  | .ambiguous symbol reason => pure (symbol, ⟨none, "ambiguous", none, .error (.machineStop reason)⟩)
  | .other symbol kind id _ =>
    let id ← definition tables id
    pure (symbol, ⟨some id, kind, none, .ok ()⟩)
  | .static symbol id declaration allocation =>
    let id ← definition tables id
    let embedded ← decodeDeclaration runtime ctx tables declaration
    unless embedded.definition == id do throw "selected exported static declaration DefId differs from its winner"
    unless embedded.symbol == symbol do throw "selected exported static declaration symbol differs from its winner"
    if let .error reason := embedded.result then
      return (symbol, ⟨some id, "static", none, .error (.unsupported s!"compiler extern-static query: {reason}")⟩)
    unless ctx.containsAllocationId allocation do throw "selected exported static allocation is absent from compiler graph"
    pure (symbol, ⟨some id, "static", some allocation, .ok ()⟩)

def prepare (runtime : RuntimeMetadata) (program : LoweredProgram) : Except String Prepared := do
  let ctx := LowerContext.ofDocument program.input
  let source := program.input.queries.runtime.foreignSymbols
  let targetResult := do
    let mut families := #[]
    for family in source.families do
      if families.contains family then throw "duplicate rustc target family"
      families := families.push family
    pure (⟨source.os, source.env, source.binaryFormat, families⟩ : TargetFacts)
  let some records := source.externDeclarations |
    pure ⟨program, runtime, .error "compiler extern-static declarations absent", targetResult, #[], #[]⟩
  let some winners := source.selectedExports |
    pure ⟨program, runtime, .error "compiler selected exports absent", targetResult, #[], #[]⟩
  let mut declarations := #[]
  for record in records do
    let entry ← decodeDeclaration runtime ctx program.compilerTables record
    if let some old := declarations.find? (·.definition == entry.definition) then
      unless old == entry do throw "conflicting exact extern-static declaration queries"
    else declarations := declarations.push entry
  let mut selected := #[]
  for record in winners do
    let (symbol, winner) ← selectedWinner runtime ctx program.compilerTables record
    if selected.any (·.symbol == symbol) then throw "duplicate selected exported symbol row"
    selected := selected.push ⟨symbol, winner⟩
  pure ⟨program, runtime, .ok (), targetResult, declarations, selected⟩

private def declaration (p : Prepared) (id : MIR.DefId) : Except String Declaration := do
  let some entry := p.declarations.find? (·.definition == id)
    | match p.sourceResult with
      | .ok () => throw "missing exact compiler extern-static declaration row"
      | .error reason => throw reason
  match entry.result with
  | .ok () => pure entry
  | .error reason => throw reason

private def stepError (reason : String) : StepError := .unsupported s!"compiler extern-static query: {reason}"

private def runtimeDeclaration (p : Prepared) (id : MIR.DefId) :
    ExternStatic.M S ExternStatic.Declaration := do
  match declaration p id with
  | .error reason => throw (stepError reason)
  | .ok entry => pure ⟨entry.symbol,entry.size,entry.align,entry.linkage⟩

private def selected (p : Prepared) (name : String) : ExternStatic.M S (Option Winner) := do
  let some entry := p.selected.find? (·.symbol == name)
    | match p.sourceResult with
      | .ok () => return none
      | .error reason => throw (stepError reason)
  match entry.winner.result with
  | .ok () => return some entry.winner
  | .error error => throw error

private def liftMemory (result : Except ε A) (showError : ε → String) : ExternStatic.M S A :=
  match result with
  | .ok value => pure value
  | .error error => throw (.invalidProgram (showError error))

/-! Build the source resolver on any persistent machine state. The caller
supplies its canonical memory/runtime views and root-pointer operation; this
lets constants and allocation-image relocations share one resolver even though
the latter intentionally run without a MIR frame. -/
def hooksOn [DecidableEq K] (p : Prepared) (image : AllocationImage.Imported)
    (memory : S → MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (externStaticState : S → ExternStatic.State)
    (checkSymbolClash : String → ExternStatic.M S Unit)
    (rootPointer : AllocId → ExternStatic.M S StrictPointer) :
    ExternStatic.ResolveHooks S Winner := by
  let pointerSize := p.runtime.target.pointerSize
  exact {
    get := do return externStaticState (← get)
    declaration := runtimeDeclaration p
    pointerSize
    checkSymbolClash
    allocationInfo := fun id => do
      let info ← liftMemory ((memory (← get)).getAllocInfo id) reprStr
      pure ⟨info.size,info.align⟩
    lookupStatic := selected p
    evalGlobal := fun winner => do
      unless winner.kind == "static" do
        throw (.undefinedBehavior "attempt to access an exported symbol that is not defined as a static")
      let some definitionId := winner.definition | throw (stepError "selected static has no exact DefId")
      let some allocation := winner.allocation | throw (stepError "selected static initializer allocation is unavailable")
      let currentMemory := memory (← get)
      unless image.source.any (·.id == allocation) do
        throw (stepError "selected static allocation is absent from canonical imported image")
      let id ← liftMemory (AllocationImage.runtimeId currentMemory allocation) id
      let some info := currentMemory.findGlobal? id | throw (stepError "selected static is absent from imported global allocations")
      match info.payload with
      | some (.static actual true false false) =>
        unless actual == definitionId do throw (.invalidProgram "selected static allocation DefId mismatch")
      | some (.static _ false _ _) => throw (.undefinedBehavior "exported symbol is not defined as a static")
      | some (.static _ _ true _) => throw (.invalidProgram "exported static unexpectedly has thread-local storage")
      | some (.static _ _ _ true) => throw (stepError "selected exported static is a foreign item")
      | _ => throw (stepError "selected static allocation payload is not a source static")
      rootPointer id
    declarationMutable := fun definitionId => do
      match declaration p definitionId with
      | .ok entry => pure entry.mutable
      | .error reason => throw (stepError reason)
    allocationMutable := fun id => do
      let info ← liftMemory ((memory (← get)).getAllocInfo id) reprStr
      pure (info.mutability == .Mut) }

def resolveOn [DecidableEq K] (p : Prepared) (image : AllocationImage.Imported)
    (memory : S → MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (externStaticState : S → ExternStatic.State)
    (checkSymbolClash : String → ExternStatic.M S Unit)
    (rootPointer : AllocId → ExternStatic.M S StrictPointer)
    (definitionId : MIR.DefId) : ExternStatic.M S StrictPointer :=
  ExternStatic.resolve (hooksOn p image memory externStaticState checkSymbolClash rootPointer)
    definitionId

/-! Actual full-interpreter adapter, including the source function-pointer
root operation and the same runtime ExternStatic storage used by GC. -/
def hooks [DecidableEq K] (p : Prepared) (image : AllocationImage.Imported)
    (checkSymbolClash : String → MachineHooks.M K U Unit)
    (functions : FunctionPointers.Hooks K U Other)
    (externStaticState : U → ExternStatic.State) :
    ExternStatic.ResolveHooks (MachineHooks.State K U) Winner :=
  hooksOn p image (fun state => state.machine.memory)
    (fun state => externStaticState state.machine.user) checkSymbolClash
    (FunctionPointers.rootPointer functions)

def resolve [DecidableEq K] (p : Prepared) (image : AllocationImage.Imported)
    (checkSymbolClash : String → MachineHooks.M K U Unit)
    (functions : FunctionPointers.Hooks K U Other)
    (externStaticState : U → ExternStatic.State) (definitionId : MIR.DefId) :
    MachineHooks.M K U (StrictPointer) :=
  ExternStatic.resolve (hooks p image checkSymbolClash functions externStaticState) definitionId

end Miri.Input.CompilerExternStatic
