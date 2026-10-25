import Miri.Memory.AllocationAccess

open Miri.ABI
open Miri.Memory

private def size (n : Nat) : Size := Size.ofBytes (UInt64.ofNat n)
private def target : PointerArithmetic := ⟨size 8⟩
private def allocId : AllocId := ⟨1, by decide⟩

inductive TestProvenance where
  | fixed (id : AllocId)
  deriving DecidableEq, Repr

structure Hooks where
  events : Array String := #[]
  resolveCount : Nat := 0
  failResolveAt : Nat := 0
  failAllocationAccess : Bool := false
  failRead : Bool := false
  failWrite : Bool := false
  deriving Repr

private def event (hooks : Hooks) (label : String) : Hooks :=
  { hooks with events := hooks.events.push label }

private def localAllocation (mutability : Mutability) (extra : Nat) :
    Allocation TestProvenance Nat := by
  let result := Allocation.fromBytes (Prov := TestProvenance)
    (Array.replicate 8 0) Align.EIGHT mutability
  have valid : result.isOk = true := by cases mutability <;> decide
  cases hresult : result with
  | error _ =>
    have impossible : False := by rw [hresult] at valid; change false = true at valid; cases valid
    exact False.elim impossible
  | ok allocation => exact allocation.withExtra extra

private def sourceAllocation (mutability : Mutability) : Allocation CtfeProvenance Unit := by
  let result := Allocation.fromBytes (Prov := CtfeProvenance)
    (Array.replicate 8 0) Align.EIGHT mutability
  have valid : result.isOk = true := by cases mutability <;> decide
  cases hresult : result with
  | error _ =>
    have impossible : False := by rw [hresult] at valid; change false = true at valid; cases valid
    exact False.elim impossible
  | ok allocation => exact allocation

private def accessHooks : AllocationAccessHooks TestProvenance Nat Unit Hooks Nat where
  resolvePointer := fun _ hooks pointer signedSize => Id.run do
    let count := hooks.resolveCount + 1
    let next := event { hooks with resolveCount := count } s!"resolve:{signedSize}"
    if next.failResolveAt == count then
      return ⟨next, .ok (.error pointer.offset.bytes)⟩
    match pointer.provenance with
    | none => return ⟨next, .ok (.error pointer.offset.bytes)⟩
    | some (.fixed id) => return ⟨next, .ok (.ok ⟨id, pointer.offset, 9⟩)⟩
  beforeAllocationAccess := fun hooks id => Id.run do
    let next := event hooks s!"alloc:{id.value}"
    if hooks.failAllocationAccess then return ⟨next, .error "alloc"⟩
    return ⟨next, .ok ()⟩
  beforeMemoryRead := fun hooks extra _ id _ _ => Id.run do
    let next := event hooks s!"read:{id.value}"
    let updated := extra + 3
    if hooks.failRead then return ⟨next, updated, .error "read"⟩
    return ⟨next, updated, .ok ()⟩
  beforeMemoryWrite := fun hooks extra _ id _ _ => Id.run do
    let next := event hooks s!"write:{id.value}"
    let updated := extra + 7
    if hooks.failWrite then return ⟨next, updated, .error "write"⟩
    return ⟨next, updated, .ok ()⟩

private def globalHooks : GlobalAllocationHooks TestProvenance Nat Unit Hooks where
  synchronizeMemory := fun _ state => state
  evaluateStaticInitializer := fun memory hooks _ => ⟨memory, hooks, .error "unexpected static"⟩
  beforeAccessGlobal := fun memory hooks id _ _ isWrite =>
    let mode := if isWrite then "write" else "read"
    ⟨memory, event hooks s!"global:{mode}:{id.value}", .ok ()⟩
  adjustGlobalAllocation := fun memory hooks id source =>
    let next := event hooks s!"adjust:{id.value}"
    ⟨memory, next, .ok (.owned (localAllocation source.mutability 5))⟩

private def mkMemory (localMutability globalMutability : Option Mutability) :
    MemoryState TestProvenance Nat Unit := Id.run do
  let locals := match localMutability with
    | none => #[]
    | some mutability => #[(allocId, LocalAllocation.mk .stack
        (localAllocation mutability 5))]
  let globals := match globalMutability with
    | none => #[]
    | some mutability => #[{
        allocId := allocId
        kind := GlobalAllocationKind.memory
        size := size 8
        align := Align.EIGHT
        mutability := mutability
        payload := some (.memory (sourceAllocation mutability))
      }]
  let empty : MemoryState TestProvenance Nat Unit := MemoryState.empty
  let withGlobals := MemoryState.setGlobalEntries empty globals
  return { withGlobals with live := locals }

private def mkPointer (offset : Nat) (valid : Bool) : Pointer (Option TestProvenance) :=
  ⟨size offset, if valid then some (.fixed allocId) else none⟩

private def showOutcome (result : PtrAllocationResult TestProvenance Nat Unit Hooks
    (Option (AllocationAccessRef TestProvenance Nat))) : String :=
  match result.outcome with
  | .ok none => "N"
  | .ok (some _) => "S"
  | .error (.hookFailure _ "alloc") => "Halloc"
  | .error (.hookFailure _ "read") => "Hread"
  | .error (.hookFailure _ "write") => "Hwrite"
  | .error (.rawAccess (.readOnlyAllocation id)) => s!"R{id.value}"
  | .error (.access (.pointerOutOfBounds id allocSize offset bytes _)) =>
      s!"B{id.value}:{allocSize.bytes.toNat}:{offset}:{bytes}"
  | .error error => s!"E{reprStr error}"

private def extraOf (memory : MemoryState TestProvenance Nat Unit) : String :=
  match memory.live.find? (fun entry => entry.1 == allocId) with
  | none => "-"
  | some entry => toString entry.2.allocation.extra

private def runCase (tag : String) (write : Bool) (bytes offset : Nat)
    (ghost valid : Bool) (localMutability globalMutability : Option Mutability)
    (failResolveAt : Nat := 0) (failAccess failRead failWrite : Bool := false) : IO Unit := do
  let hooks : Hooks := { events := #[], resolveCount := 0, failResolveAt := failResolveAt, failAllocationAccess := failAccess, failRead := failRead, failWrite := failWrite }
  let memory := mkMemory localMutability globalMutability
  let pointer := mkPointer offset valid
  let result := if write then
      AllocationAccess.getPtrAllocMut memory hooks target pointer (size bytes) ghost
        (some ()) globalHooks accessHooks
    else
      AllocationAccess.getPtrAlloc memory hooks target pointer (size bytes) ghost
        (some ()) globalHooks accessHooks
  let eventText := String.intercalate "," result.hooks.events.toList
  IO.println s!"A {tag} {showOutcome result} [{eventText}] {extraOf result.memory}"

def main : IO Unit := do
  runCase "zero_read" false 0 1 false true (some .Mut) none
  runCase "zero_read_second_dangling" false 0 1 false true none none 1
  runCase "zero_write" true 0 1 false true (some .Mut) none
  runCase "ghost_read" false 2 2 true true (some .Mut) none
  runCase "ghost_write" true 2 2 true true (some .Mut) none
  runCase "readonly_oob_write" true 2 7 false true (some .Not) none
  runCase "global_readonly_oob_write" true 2 7 false true none (some .Not)
  runCase "global_oob_write" true 2 7 false true none (some .Mut)
  runCase "partial_read_failure" false 2 2 false true (some .Mut) none 0 false true
  runCase "partial_write_failure" true 2 2 false true (some .Mut) none 0 false false true
  runCase "allocation_hook_failure" false 2 2 false true (some .Mut) none 0 true
  runCase "read_second_resolve_dangling" false 2 2 false true (some .Mut) none 2
