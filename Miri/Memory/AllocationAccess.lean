import Miri.Memory.MemoryState

/-! Bounds-checked allocation access from pinned interpreter memory.rs.
Actual global materialization precedes bounds checking. Machine access hooks
remain explicit, and retain updated allocation extras even when they fail.
These helpers do not check alignment or perform byte loads/stores. -/
namespace Miri.Memory
open Miri.ABI

structure AllocationExtraHookResult (HookState Extra : Type) where
  state : HookState
  extra : Extra
  outcome : Except String Unit

structure AllocationAccessHooks (Prov Extra MachineKind HookState ProvExtra : Type) where
  /-- Outer error means unavailable machine semantics; inner error is the
  source's integer address that could not be resolved. -/
  resolvePointer : MemoryState Prov Extra MachineKind → HookState →
    Pointer (Option Prov) → Int →
    MachineHookResult HookState (Except UInt64 (ResolvedPointer ProvExtra))
  beforeAllocationAccess : HookState → AllocId → MachineHookResult HookState Unit
  beforeMemoryRead : HookState → Extra → Pointer (Option Prov) →
    AllocId → ProvExtra → AllocRange → AllocationExtraHookResult HookState Extra
  beforeMemoryWrite : HookState → Extra → Pointer (Option Prov) →
    AllocId → ProvExtra → AllocRange → AllocationExtraHookResult HookState Extra

structure AllocationAccessRef (Prov Extra : Type) where
  allocId : AllocId
  range : AllocRange
  allocation : Allocation Prov Extra

inductive PtrAllocationError where
  | access (reason : AccessError)
  | rawAccess (reason : MemoryAccessError)
  | hookFailure (hook message : String)
  | cacheUpdate (reason : AllocationLookupError)
  deriving DecidableEq, Repr

structure PtrAllocationResult (Prov Extra MachineKind HookState α : Type) where
  memory : MemoryState Prov Extra MachineKind
  hooks : HookState
  /-- Snapshot also retained on failure for borrowed global allocation extras.
  Miri-owned allocations are simultaneously updated in `memory.live`. -/
  touched : Option (AllocationAccessRef Prov Extra)
  outcome : Except PtrAllocationError α

namespace AllocationAccess
variable {Prov Extra MachineKind HookState ProvExtra : Type}

/-- Pointer access can finish during resolution or reach the memory hook
after selecting and checking an allocation. -/
inductive PreparedPtrAllocation (P E K H X : Type) where
  | finished (result : PtrAllocationResult P E K H (Option (AllocationAccessRef P E)))
  | access (memory : MemoryState P E K) (hooks : H) (provenance : X)
      (reference : AllocationAccessRef P E)

/-- Commit an access hook's updated allocation extra before reporting its
success or failure. Both outcomes retain the updated snapshot. -/
def finishCheckedAccess [DecidableEq MachineKind] (write : Bool) (memory : MemoryState Prov Extra MachineKind)
    (reference : AllocationAccessRef Prov Extra) (access : AllocationExtraHookResult HookState Extra) :
    PtrAllocationResult Prov Extra MachineKind HookState (Option (AllocationAccessRef Prov Extra)) :=
  let updated := {reference with allocation := reference.allocation.setExtra access.extra}
  let cached := if memory.live.any (fun entry => entry.1 == reference.allocId) then
      memory.setLiveAllocation reference.allocId updated.allocation
    else .ok memory
  match cached with
  | .error error => ⟨memory, access.state, some updated, .error (.cacheUpdate error)⟩
  | .ok after =>
    let outcome := match access.outcome with
      | .ok () => .ok (some updated)
      | .error message =>
        .error (.hookFailure (if write then "beforeMemoryWrite" else "beforeMemoryRead") message)
    ⟨after, access.state, some updated, outcome⟩

/-- Unified implementation of source `get_ptr_alloc` and `get_ptr_alloc_mut`.
`write` selects exactly their different raw lookup and access-hook order. -/
def preparePtrAllocation [DecidableEq MachineKind]
    (initialMemory : MemoryState Prov Extra MachineKind) (initialHooks : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Size)
    (ghostMode : Bool) (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra)
    (write : Bool) :
    PreparedPtrAllocation Prov Extra MachineKind HookState ProvExtra := Id.run do
  let mut memory := initialMemory
  let mut hookState := initialHooks
  let signedSize ← match sizeAsI64 size with
    | .ok amount => pure amount
    | .error error => return .finished ⟨memory, hookState, none, .error (.access error)⟩
  let mut checked : Option (ResolvedPointer ProvExtra × AllocationAccessRef Prov Extra) := none
  if signedSize != 0 then
    let resolution := accessHooks.resolvePointer memory hookState ptr signedSize
    hookState := resolution.state
    let resolved ← match resolution.outcome with
      | .error message => return .finished ⟨memory, hookState, none,
          .error (.hookFailure "ptrTryGetAllocId" message)⟩
      | .ok (.error address) => return .finished ⟨memory, hookState, none,
          .error (.access (.danglingIntegerPointer address signedSize .memoryAccess))⟩
      | .ok (.ok resolved) => pure resolved
    let raw := if write then
        MemoryLifecycle.getAllocRawMut memory hookState resolved.allocId globalKind globalHooks
      else MemoryLifecycle.getAllocRaw memory hookState resolved.allocId globalKind globalHooks
    memory := raw.memory
    hookState := raw.hooks
    let allocation ← match raw.outcome with
      | .ok allocation => pure allocation
      | .error error => return .finished ⟨memory, hookState, none, .error (.rawAccess error)⟩
    let reference : AllocationAccessRef Prov Extra :=
      ⟨resolved.allocId, allocRange resolved.offset size, allocation⟩
    match checkedBounds target resolved.allocId allocation.byteSize resolved.offset signedSize .memoryAccess with
    | .error error => return .finished ⟨memory, hookState, some reference, .error (.access error)⟩
    | .ok () => checked := some (resolved, reference)
  if !ghostMode then
    let accessId ← if write then
        pure (checked.map fun (_, reference) => reference.allocId)
      else do
        -- The source deliberately resolves again, including size-zero reads.
        let resolution := accessHooks.resolvePointer memory hookState ptr signedSize
        hookState := resolution.state
        match resolution.outcome with
        | .error message => return .finished ⟨memory, hookState, checked.map Prod.snd,
            .error (.hookFailure "ptrTryGetAllocId" message)⟩
        | .ok (.error _) => pure none
        | .ok (.ok resolved) => pure (some resolved.allocId)
    if let some accessId := accessId then
      let access := accessHooks.beforeAllocationAccess hookState accessId
      hookState := access.state
      if let .error message := access.outcome then
        return .finished ⟨memory, hookState, checked.map Prod.snd,
          .error (.hookFailure "beforeAllocAccess" message)⟩
    if let some (resolved, reference) := checked then
      return .access memory hookState resolved.extra reference
  let reference := checked.map Prod.snd
  return .finished ⟨memory, hookState, reference, .ok reference⟩

/-- Execute the memory hook selected by pointer preparation and commit its
result. Early failures and zero-sized accesses retain their original result. -/
def finishPreparedAccess [DecidableEq MachineKind]
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra)
    (write : Bool) (ptr : Pointer (Option Prov))
    (prepared : PreparedPtrAllocation Prov Extra MachineKind HookState ProvExtra) :
    PtrAllocationResult Prov Extra MachineKind HookState (Option (AllocationAccessRef Prov Extra)) :=
  match prepared with
  | .finished result => result
  | .access memory hooks provenance reference =>
    let access := if write then
      accessHooks.beforeMemoryWrite hooks reference.allocation.extra ptr reference.allocId provenance reference.range
    else
      accessHooks.beforeMemoryRead hooks reference.allocation.extra ptr reference.allocId provenance reference.range
    finishCheckedAccess write memory reference access

def getPtrAllocation [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooks : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Size)
    (ghost : Bool) (kind : Option MachineKind)
    (globals : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (access : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra) (write : Bool) :
    PtrAllocationResult Prov Extra MachineKind HookState (Option (AllocationAccessRef Prov Extra)) :=
  finishPreparedAccess access write ptr
    (preparePtrAllocation memory hooks target ptr size ghost kind globals access write)

def getPtrAlloc [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Size)
    (ghostMode : Bool) (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra) :=
  getPtrAllocation memory hooksState target ptr size ghostMode globalKind globalHooks accessHooks false

def getPtrAllocMut [DecidableEq MachineKind]
    (memory : MemoryState Prov Extra MachineKind) (hooksState : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Size)
    (ghostMode : Bool) (globalKind : Option MachineKind)
    (globalHooks : GlobalAllocationHooks Prov Extra MachineKind HookState)
    (accessHooks : AllocationAccessHooks Prov Extra MachineKind HookState ProvExtra) :=
  getPtrAllocation memory hooksState target ptr size ghostMode globalKind globalHooks accessHooks true

end AllocationAccess
end Miri.Memory

namespace Miri.Memory.AllocationAccess
open Miri.ABI
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
variable {P E K H X : Type} [DecidableEq K]
/-- Internal edges compose the production positive mutable-access path. -/
theorem live_mut_of_edges (memory : MemoryState P E K) (hooks : H)
    (target : PointerArithmetic) (ptr : Pointer (Option P)) (size : Size)
    (kind : Option K) (global : GlobalAllocationHooks P E K H)
    (access : AllocationAccessHooks P E K H X) (id : AllocId)
    (entry : LocalAllocation P E K) (provenance : X) (amount : Int)
    (signed : sizeAsI64 size = .ok amount) (nonzero : amount ≠ 0)
    (resolve : access.resolvePointer memory hooks ptr amount = ⟨hooks,.ok (.ok ⟨id,Size.ZERO,provenance⟩)⟩)
    (live : memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (mutable : entry.allocation.mutability = .Mut)
    (synchronize : global.synchronizeMemory memory hooks = hooks)
    (bounds : checkedBounds target id entry.allocation.byteSize Size.ZERO amount .memoryAccess = .ok ())
    (before : access.beforeAllocationAccess hooks id = ⟨hooks,.ok ()⟩)
    (write : access.beforeMemoryWrite hooks entry.allocation.extra ptr id provenance (allocRange Size.ZERO size) =
      ⟨hooks,entry.allocation.extra,.ok ()⟩)
    (last : (memory.live.filter (fun row => row.1 != id)).push (id,entry) = memory.live) :
    getPtrAllocMut memory hooks target ptr size false kind global access =
      ⟨memory,hooks,some ⟨id,allocRange Size.ZERO size,entry.allocation⟩,
        .ok (some ⟨id,allocRange Size.ZERO size,entry.allocation⟩)⟩ := by
  have sameExtra : entry.allocation.setExtra entry.allocation.extra = entry.allocation := by
    cases entry.allocation; rfl
  have cache : memory.setLiveAllocation id entry.allocation = .ok memory := by
    rw [MemoryState.setLiveAllocation_of_find memory id entry entry.allocation live]
    simp only [last]
  have raw : MemoryLifecycle.getAllocRawMut memory hooks id kind global =
      ⟨memory,hooks,.ok entry.allocation⟩ := by
    simp [MemoryLifecycle.getAllocRawMut,live,mutable,synchronize]
  unfold getPtrAllocMut getPtrAllocation preparePtrAllocation
  rw [signed]
  dsimp only [Id.run,bind,Bind.bind,pure,Pure.pure]
  simp only [nonzero,bne_iff_ne,↓reduceIte]
  rw [resolve]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  rw [raw]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  rw [bounds]
  simp only [bind,Bind.bind,pure,Pure.pure]
  simp only [nonzero,↓reduceIte,Bool.not_false,Option.map_some]
  rw [before]
  dsimp only [bind,Bind.bind,pure,Pure.pure]
  simp only [ite_eq_left nonzero]
  simp only [finishPreparedAccess, finishCheckedAccess, ↓reduceIte, write, sameExtra]
  split <;> simp_all [cache,bind,Bind.bind,pure,Pure.pure]
end Miri.Memory.AllocationAccess

namespace Miri.Memory.AllocationAccess
open Miri.ABI

variable {P E K H X : Type} [DecidableEq K]

/-- A nonzero, bounds-checked access in normal execution reaches the
actual memory hook. Raw lookup may materialize a global and may update
the initial hook state. A read resolves the pointer again before probing. -/
theorem getPtrAlloc_checked
    (write : Bool) (memory rawMemory : MemoryState P E K) (hooks resolvedHooks rawHooks ready : H)
    (target : PointerArithmetic) (ptr : Pointer (Option P)) (size : Size) (kind : Option K)
    (global : GlobalAllocationHooks P E K H) (access : AllocationAccessHooks P E K H X)
    (resolved probed : ResolvedPointer X) (allocation : Allocation P E) (amount : Int) (probeState : H)
    (signed : sizeAsI64 size = .ok amount) (nonzero : amount ≠ 0)
    (resolve : access.resolvePointer memory hooks ptr amount = ⟨resolvedHooks, .ok (.ok resolved)⟩)
    (raw : (if write then MemoryLifecycle.getAllocRawMut memory resolvedHooks resolved.allocId kind global
      else MemoryLifecycle.getAllocRaw memory resolvedHooks resolved.allocId kind global) =
        ⟨rawMemory, rawHooks, .ok allocation⟩)
    (bounds : checkedBounds target resolved.allocId allocation.byteSize resolved.offset amount .memoryAccess = .ok ())
    (probe : write = false → access.resolvePointer rawMemory rawHooks ptr amount =
      ⟨probeState, .ok (.ok probed)⟩)
    (before : access.beforeAllocationAccess (if write then rawHooks else probeState)
      (if write then resolved.allocId else probed.allocId) =
      ⟨ready,.ok ()⟩) :
    (if write then getPtrAllocMut memory hooks target ptr size false kind global access
      else getPtrAlloc memory hooks target ptr size false kind global access) =
      let range := allocRange resolved.offset size
      finishCheckedAccess write rawMemory ⟨resolved.allocId, range, allocation⟩
        ((if write then access.beforeMemoryWrite else access.beforeMemoryRead) ready
          allocation.extra ptr resolved.allocId resolved.extra range) := by
  have same :
      (if write then getPtrAllocMut memory hooks target ptr size false kind global access
        else getPtrAlloc memory hooks target ptr size false kind global access) =
        getPtrAllocation memory hooks target ptr size false kind global access write := by
    cases write <;> rfl
  rw [same]
  unfold getPtrAllocation preparePtrAllocation
  rw [signed]
  dsimp only [Id.run, bind, Bind.bind, pure, Pure.pure]
  simp only [bne_iff_ne, ite_eq_left nonzero]
  rw [resolve]
  dsimp only
  rw [raw]
  dsimp only
  rw [bounds]
  dsimp only
  cases write
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false]
    rw [probe rfl]
    dsimp only
    rw [show access.beforeAllocationAccess probeState probed.allocId = ⟨ready, .ok ()⟩ from before]
    dsimp only
    rfl
  · simp only [↓reduceIte, Bool.not_false, Option.map_some]
    rw [show access.beforeAllocationAccess rawHooks resolved.allocId = ⟨ready, .ok ()⟩ from before]
    dsimp only
    rfl

end Miri.Memory.AllocationAccess
