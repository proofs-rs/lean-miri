import Miri.Interpreter.LocalAccess
import Miri.Interpreter.Step

open Miri Miri.ABI Miri.Memory Miri.Interpreter

/-! Restricted fixture memory: one fresh, unique, mutable return allocation,
single-thread access, no globals, no exposed addresses, no dynamic layouts.
These policies are fixture assumptions, not a general Miri machine. -/
namespace ReturnMemory
structure State where
  memory : MemoryState AllocId Unit Unit
  events : Array String := #[]

private def globalHooks : GlobalAllocationHooks AllocId Unit Unit (Array String) := {
  synchronizeMemory := fun _ state => state
  evaluateStaticInitializer := fun memory state _ => ⟨memory, state, .error "fixture has no statics"⟩
  beforeAccessGlobal := fun memory state _ _ _ _ => ⟨memory, state, .error "fixture has no globals"⟩
  adjustGlobalAllocation := fun memory state _ _ => ⟨memory, state, .error "fixture has no globals"⟩ }

private def accessHooks : AllocationAccessHooks AllocId Unit Unit (Array String) Unit := {
  resolvePointer := fun _ state pointer _ =>
    match pointer.provenance with
    | some id => ⟨state.push "resolve-return", .ok (.ok ⟨id, pointer.offset, ()⟩)⟩
    | none => ⟨state, .error "fixture does not resolve address-only pointers"⟩
  beforeAllocationAccess := fun state _ => ⟨state.push "return-allocation", .ok ()⟩
  beforeMemoryRead := fun state extra _ _ _ _ => ⟨state.push "read-return", extra, .ok ()⟩
  beforeMemoryWrite := fun state extra _ _ _ _ => ⟨state.push "write-return", extra, .ok ()⟩ }

private def dynamicLayout : DynamicLayoutResolver AllocId Unit Unit (Array String) :=
  fun memory hooks _ => ⟨memory, hooks, .error "fixture does not support unsized return layouts"⟩

private def runtime (target : TargetDataLayout) : RuntimeTargetDataLayout :=
  { RuntimeTargetDataLayout.default with base := target }

private def failure (error : MemoryOperandError) : StepError :=
  .callback s!"return memory access: {repr error}"

def create (target : TargetDataLayout) (layout : LocalLayout) :
    Except StepError (State × MemoryOperandPlace AllocId) := do
  if target.pointerWidth != .w64 then
    throw (.unsupported "fixture return memory requires 64-bit target pointer layout")
  if !layout.layout.isSized || layout.layout.size.bytes != 4 then
    throw (.unsupported "fixture return memory requires sized u32")
  let empty : MemoryState AllocId Unit Unit := MemoryState.empty
  let (memory, reserved) := empty.reserveAllocId
  let id ← reserved.mapError fun error => .callback s!"return allocation ID: {repr error}"
  let allocation ← (Allocation.fromBytes (Prov := AllocId)
    (Array.replicate 4 0) layout.layout.align.abi .Mut).mapError fun error =>
      .callback s!"return allocation: {error}"
  let allocation ← match Allocation.writeUninit
      (allocRange Size.ZERO layout.layout.size) (Size.fromBits target.pointerWidth.bits) allocation with
    | .ok () allocation => pure allocation
    | .error error _ => throw (.callback s!"return initialization: {error}")
  let memory := { memory with live := #[(id, ⟨.stack, allocation⟩)] }
  return (⟨memory, #[]⟩, ⟨⟨⟨Size.ZERO, some id⟩, .none, none⟩, localMemoryLayout layout⟩)

def write (target : TargetDataLayout) (state : State) (place : MemoryOperandPlace AllocId)
    (value : Immediate AllocId) : State × Except StepError Unit :=
  let result := writeImmediateToMplaceNoValidate state.memory state.events value place
    (runtime target) false none globalHooks accessHooks dynamicLayout (fun _ => false)
  (⟨result.memory, result.hooks⟩, result.outcome.mapError failure)

def read (target : TargetDataLayout) (state : State) (place : MemoryOperandPlace AllocId) :
    State × Except StepError (ImmediateValue AllocId) :=
  let result := readImmediate state.memory state.events (.indirect place.mplace) place.layout
    (runtime target) false none globalHooks accessHooks dynamicLayout
  (⟨result.memory, result.hooks⟩, result.outcome.mapError failure)
end ReturnMemory
