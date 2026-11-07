import Miri.Input.RuntimeProgram
import Miri.Input.CompilerLinkSections

/-! Exact compiler support for `machine.rs::extern_static_pointer`.
Declaration metadata is keyed by shared DefId identity. Exported-static
resolution retains the source-selected symbol winner and its allocation ID;
the winner is materialized only through the canonical imported global table.
-/
namespace Miri.Input.CompilerExternStatic
open Lean Miri.ABI Miri.Memory Miri.Interpreter

abbrev Declaration := ExternStaticDeclarationData
abbrev Winner := ExternStaticWinnerData
abbrev Selected := ExternStaticSelectedData
abbrev TargetFacts := CompilerTargetFactsData

structure Prepared where
  owner : RuntimeProgram
  sourceStatus : Except String Unit
  targetFacts : Except String TargetFacts
  declarations : Array Declaration
  selected : Array Selected

@[inline] def Prepared.program (prepared : Prepared) : LoweredProgram := prepared.owner.program
@[inline] def Prepared.runtime (prepared : Prepared) : RuntimeMetadata := prepared.owner.runtime

def Prepared.withProgram (prepared : Prepared) (program : LoweredProgram) : Prepared :=
  {prepared with owner := prepared.owner.withProgram program}

def prepare (owner : RuntimeProgram) : Except String Prepared := do
  let program := owner.program
  let runtime := owner.runtime
  let data ← program.input.mirTables.externStatics
  return ⟨owner,data.sourceStatus,data.targetFacts,data.declarations,data.selected⟩

private def declaration (p : Prepared) (id : MIR.DefId) : Except String Declaration := do
  let some entry := p.declarations.find? (·.definition == id)
    | match p.sourceStatus with
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
    | match p.sourceStatus with
      | .ok () => return none
      | .error reason => throw (stepError reason)
  match entry.winner.status with
  | "supported" => return some entry.winner
  | "ambiguous" => throw (.machineStop entry.winner.reason)
  | _ => throw (stepError entry.winner.reason)

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
