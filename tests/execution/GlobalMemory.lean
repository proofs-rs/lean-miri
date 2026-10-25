import Miri.Input.AllocationImage
import Miri.Interpreter.Constant
import Miri.Interpreter.LocalAccess
import Miri.Interpreter.Step

open Miri Miri.ABI Miri.Memory Miri.Interpreter

/-! Fixture global memory: compiler-imported immutable DATA plus a fresh,
unique mutable return allocation. Single thread, no extern/TLS, no exposed
addresses, no dynamic layouts. CTFE provenance flags and remapped allocation
identity are preserved. These are fixture policies, not a full Miri machine. -/
namespace GlobalMemory
structure State where
  memory : MemoryState CtfeProvenance Unit Unit
  events : Array String := #[]
  image : Input.AllocationImage.Imported

private def staticQueries : Input.AllocationImage.Queries := {
  staticInfo := fun source => do
    if source.definitionPath != "DATA" || source.threadLocal then throw "unknown fixture static declaration"
    let some initializer := source.initializer | throw "fixture static requires its compiler initializer"
    let size ← Input.RuntimeMetadata.size initializer.sizeBytes |>.mapError toString
    let align ← Input.RuntimeMetadata.alignment initializer.alignBytes |>.mapError toString
    if initializer.mutability != .immutable then throw "fixture static must be immutable"
    return ⟨size,align,.Not,true,false⟩ }

def globalHooks (image : Input.AllocationImage.Imported) : GlobalAllocationHooks CtfeProvenance Unit Unit (Array String) := {
  synchronizeMemory := fun _ state => state
  evaluateStaticInitializer := fun memory state definition =>
    let result := image.evaluateStaticInitializer (state.push "initializer") definition
    ⟨memory,result.state,result.outcome⟩
  beforeAccessGlobal := fun memory state _ _ _ _ => ⟨memory, state.push "global-access", .ok ()⟩
  adjustGlobalAllocation := fun memory state _ allocation => ⟨memory, state.push "global-adjust", .ok (.owned allocation)⟩ }

def accessHooks : AllocationAccessHooks CtfeProvenance Unit Unit (Array String) Unit := {
  resolvePointer := fun _ state pointer _ =>
    match pointer.provenance with
    | some id => ⟨state.push "resolve", .ok (.ok ⟨id.allocId, pointer.offset, ()⟩)⟩
    | none => ⟨state, .error "fixture does not resolve address-only pointers"⟩
  beforeAllocationAccess := fun state _ => ⟨state.push "allocation", .ok ()⟩
  beforeMemoryRead := fun state extra _ _ _ _ => ⟨state.push "read", extra, .ok ()⟩
  beforeMemoryWrite := fun state extra _ _ _ _ => ⟨state.push "write", extra, .ok ()⟩ }

def dynamicLayout : DynamicLayoutResolver CtfeProvenance Unit Unit (Array String) :=
  fun memory hooks _ => ⟨memory, hooks, .error "fixture does not support unsized return layouts"⟩

private def failure (error : MemoryOperandError) : StepError :=
  .callback s!"return memory access: {repr error}"

def create (runtime : RuntimeTargetDataLayout) (definitions : Array Input.DefinitionId)
    (allocations : Array Input.AllocationNode) (layout : LocalLayout) :
    Except StepError (State × MemoryOperandPlace CtfeProvenance) := do
  if runtime.base.pointerWidth != .w64 || !layout.layout.isSized || layout.layout.size.bytes != 4 then
    throw (.unsupported "fixture root return requires x64 u32")
  let empty : MemoryState CtfeProvenance Unit Unit := { MemoryState.empty with nextAllocId := 100 }
  let imported := Input.AllocationImage.importGraph runtime definitions staticQueries allocations empty
  let image ← imported.outcome.mapError StepError.invalidProgram
  let (memory,reserved) := imported.memory.reserveAllocId
  let id ← reserved.mapError (fun e => .invalidProgram (reprStr e))
  let provenance ← CtfeProvenance.fromAllocId id |>.mapError (fun e => .invalidProgram (reprStr e))
  let allocation ← Allocation.fromBytes (Prov := CtfeProvenance) (Array.replicate 4 0) layout.layout.align.abi .Mut
    |>.mapError (fun e => .invalidProgram (toString e))
  let allocation ← match allocation.writeUninit (allocRange Size.ZERO layout.layout.size) runtime.pointerSize with
    | .ok () allocation => pure allocation
    | .error e _ => throw (.invalidProgram (toString e))
  let memory := { memory with live := memory.live.push (id,⟨.stack,allocation⟩) }
  return (⟨memory,#[],image⟩,⟨⟨⟨Size.ZERO,some provenance⟩,.none,none⟩,localMemoryLayout layout⟩)

def write (runtime : RuntimeTargetDataLayout) (state : State) (place : MemoryOperandPlace CtfeProvenance)
    (value : Immediate CtfeProvenance) : State × Except StepError Unit :=
  let result := writeImmediateToMplaceNoValidate state.memory state.events value place
    runtime false (some ()) (globalHooks state.image) accessHooks dynamicLayout (fun _ => false)
  (⟨result.memory, result.hooks,state.image⟩, result.outcome.mapError failure)

def read (runtime : RuntimeTargetDataLayout) (state : State) (place : MemoryOperandPlace CtfeProvenance) :
    State × Except StepError (ImmediateValue CtfeProvenance) :=
  let result := readImmediate state.memory state.events (.indirect place.mplace) place.layout
    runtime false (some ()) (globalHooks state.image) accessHooks dynamicLayout
  (⟨result.memory, result.hooks,state.image⟩, result.outcome.mapError failure)
def context (runtime : RuntimeTargetDataLayout) (image : Input.AllocationImage.Imported) : LocalReadContext CtfeProvenance Unit Unit (Array String) Unit := {
  runtime, ghostMode := false, globalKind := some (), globalHooks := globalHooks image,
  accessHooks, dynamicLayout }

def validate (runtime : RuntimeTargetDataLayout) (state : State) (place : MemoryOperandPlace CtfeProvenance) :
    State × Except StepError Unit :=
  let result := getPlaceAlloc state.memory state.events place runtime false (some ())
    (globalHooks state.image) accessHooks dynamicLayout
  (⟨result.memory,result.hooks,state.image⟩,result.outcome.map (fun _ => ()) |>.mapError failure)

end GlobalMemory
