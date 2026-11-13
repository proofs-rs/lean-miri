import Miri.Input.EvalPreparation
import Miri.Input.EvalEntryMachine
import Miri.Input.CompilerGlobals
import Miri.Input.CompilerContextSpan
import Miri.Input.CompilerAllocIdWorld
import Miri.Input.Decoder
import Miri.Input.CompilerInitialAllocationWorld
import Miri.Input.CompilerInitialAllocationSymbolBridge
import Miri.Input.CompilerInitialAllocationStaticMaterial

/-! Initial compiler/image preparation for the canonical entry machine. The
allocation import is deliberately not hidden in Except: failed registration
retains the consumed allocation identities and successfully imported prefix. -/
namespace Miri.Input.CompilerInitialAllocationPreparation
open Lean Miri.Memory Miri.Interpreter
structure Prepared where
  compiler : CompilerProviders.Prepared
  image : AllocationImage.Imported
  types : RuntimeArrayTypes.World
  layouts : EvalEntryMachine.Layouts
  dummySpan : Miri.MIR.SpanRef
  snapshot : CompilerInitialAllocation.Snapshot
  initialWorld : CompilerInitialAllocation.AllocatorWorld Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind

structure Attempt where
  memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind
  outcome : Except String Prepared

/-- Compiler table preparation precedes allocation registration. All consumers
share its final identity tables; graph definitions may not be appended only to
an isolated image view. Primitive layouts and the persistent runtime type world
are required evidence, never inferred from storage sizes. -/
def prepareProfiled (profile : Lean.Options) (budget run : Nat)
    (rawSnapshot : Json)
    (input : LoweredProgram) : Attempt := Id.run do
  let empty : MemoryState Provenance Miri.TreeBorrows.BorrowTree MiriMemoryKind := .empty
  let setup ← match EvalPreparation.prepareCompilerProfiled profile input with
    | .ok value => pure value
    | .error error => return ⟨empty,.error error⟩
  let compiler := setup.compiler
  let types := setup.types
  let layouts := setup.layouts
  let dummySpan := setup.dummySpan
  if compiler.program.input.compilerAllocIdWorld.isSome then
    return ⟨empty,.error "initial snapshot cannot coexist with prepared allocator profile"⟩
  let some target := compiler.program.input.runtimeTargetDataLayout
    | return ⟨empty,.error "initial snapshot target evidence absent"⟩
  let (snapshot,snapshotTypes) ← match CompilerInitialAllocation.SymbolBridge.decode
      (UInt64.ofNat types.arena.pointerBytes) (target.endian == "little") rawSnapshot types.arena with
    | .ok value => pure value
    | .error error => return ⟨empty,.error s!"initial source symbol World: {error}"⟩
  let (symbols,snapshotTypes) ← match CompilerInitialAllocation.StaticMaterial.prepare compiler.runtime snapshot snapshotTypes with
    | .ok value => pure value
    | .error error => return ⟨empty,.error s!"initial static source layout: {error}"⟩
  let types := {types with arena := snapshotTypes}
  -- Frozen IDs were already reserved by the compiler before this execution.
  -- Bootstrap installs their runtime representation atomically; only later
  -- actual machine reservations have irreversible source-counter effects.
  let (bootstrap,initialWorld) := CompilerInitialAllocation.installAtomic budget symbols run snapshot {memory := empty}
  match bootstrap with
  | .ok () => pure ()
  | .error error => return ⟨initialWorld.memory,.error s!"initial compiler snapshot: {error}"⟩
  -- The final exporter graph is observed metadata, not the initial compiler heap.
  -- No post-query allocation is preloaded. Future demand import must extend the
  -- explicit source/runtime crosswalk and preserve the separate graph namespace.
  let imported := AllocationImage.importGraph compiler.runtime.target
    compiler.program.compilerTables.definitions CompilerGlobals.queries #[] initialWorld.memory
  match imported.outcome with
  | .error error => return ⟨imported.memory,.error error⟩
  | .ok image =>
    return ⟨imported.memory,.ok ⟨compiler,image,types,layouts,dummySpan,snapshot,
      {initialWorld with memory := imported.memory}⟩⟩

end Miri.Input.CompilerInitialAllocationPreparation
