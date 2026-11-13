import Miri.Input.CompilerInitialAllocationStore
import Miri.Input.CtfeQueryBridge

/-! Scratch-only actual shared-counter operations for typed function/vtable
symbols and non-dedup query Memory roots. Depends on the CTFE counter overlay,
not yet on the production compiler factory. No old query catalog is consulted. -/
namespace Miri.Input.CompilerInitialAllocation.VTableActions
open Miri.Memory Miri.ABI
set_option autoImplicit false
variable {P E K : Type}

/-- Must validate source type/instance keys in the same canonical execution
universe. Payload construction receives the REAL newly issued ID, never a
placeholder later relabeled as an allocation. -/
structure SymbolSource where
  validate : GlobalKey → Except String Unit
  materialize : GlobalKey → AllocId → Except String GlobalAllocation

private def active (run : Nat) (world : AllocatorWorld P E K) : Except String Unit := do
  if world.memory.sourceAllocIdWorldActive then throw "prepared/initial allocator profiles conflict"
  unless world.memory.activeInitialCompilerRun == some run && world.runs.any (·.1 == run) do
    throw "source vtable requires the actual complete active compiler run"
  let some supply := world.memory.initialCompilerRuns.find? (·.token == run)
    | throw "source vtable active compiler supply absent"
  if supply.exhausted || world.memory.idSupplyExhausted then throw "source vtable compiler counter is fatal"

/-- The central reserve retains fetch-add/overflow effects on EVERY outcome.
The raw source crosswalk is copied from that boundary, never guessed. -/
private def reserve (run : Nat) (world : AllocatorWorld P E K) :
    Except String AllocId × AllocatorWorld P E K := Id.run do
  let (memory,result) := world.memory.reserveAllocId
  let advanced := world.store.withMemory memory
  let id ← match result with
    | .error error => return (.error s!"source vtable shared reserve: {reprStr error}",advanced)
    | .ok id => pure id
  let some _ := memory.initialCompilerSource? run id
    | return (.error "source vtable shared reserve omitted raw identity",advanced)
  return (.ok id,advanced)

def internTyped (target : RuntimeTargetDataLayout) (source : SymbolSource) (run : Nat) (key : GlobalKey) (salt : UInt64)
    (world : AllocatorWorld P E K) : Except String AllocId × AllocatorWorld P E K := Id.run do
  match active run world with | .error error => return (.error error,world) | .ok _ => pure ()
  let expected ← match key with
    | .function _ => pure GlobalAllocationKind.function
    | .vtable .. => pure GlobalAllocationKind.vtable
    | _ => return (.error "typed vtable interner only accepts exact function/vtable keys",world)
  match source.validate key with | .error error => return (.error error,world) | .ok _ => pure ()
  if let some id := lookupDedup world run key salt then return (.ok id,world)
  let (reserved,world) := reserve run world
  let id ← match reserved with | .error error => return (.error error,world) | .ok id => pure id
  let global ← match source.materialize key id with
    | .error error => return (.error error,world)
    | .ok global => pure global
  unless global.allocId == id && global.kind == expected && global.size == Size.ZERO && global.mutability == .Not do
    return (.error "source symbolic material capability returned a mismatched real allocation",world)
  let alignment := if expected == .function then Align.ONE else target.defaultAddressSpacePointerSpec.pointerAlign
  unless global.align == alignment do
    return (.error "source symbolic material capability returned wrong source alignment",world)
  let payloadOk := match expected,global.payload with
    | .function,some .function | .vtable,some .vtable => true
    | _,_ => false
  unless payloadOk do return (.error "source symbolic material capability omitted typed payload",world)
  let committed := {world with
    memory := world.memory.pushGlobal global
    typedDedup := world.typedDedup.push ⟨run,key,salt,id⟩
    symbolic := world.symbolic.push (id,key)}
  return (.ok id,committed)

/-- reserve_and_set_memory_alloc always consumes a fresh ID, even for equal
bytes/provenance. It installs NO typed dedup row. Query memoization is separate. -/
def reserveMemory (target : TargetDataLayout) (run : Nat)
    (allocation : Allocation CtfeProvenance Unit) (world : AllocatorWorld P E K) :
    Except String AllocId × AllocatorWorld P E K := Id.run do
  match active run world with | .error error => return (.error error,world) | .ok _ => pure ()
  unless allocation.mutability == .Not do return (.error "source vtable query memory is mutable",world)
  let bytes ← match allocation.inspectWithUninitAndPtrOutsideInterpreter 0 allocation.len with
    | .error error => return (.error s!"source vtable memory image: {error}",world)
    | .ok value => pure value
  let alignment ← match allocation.align.bytes with
    | .error error => return (.error s!"source vtable memory alignment: {error}",world)
    | .ok value => pure value
  let rawResult : Except String (ProvenanceMap CtfeProvenance) := do
    let convert (provenance : CtfeProvenance) : Except String CtfeProvenance := do
      let some raw := world.memory.initialCompilerSource? run provenance.allocId
        | throw "source vtable provenance runtime identity lacks actual source crosswalk"
      let some source := AllocId.ofUInt64 raw
        | throw "source vtable provenance raw identity is zero"
      (CtfeProvenance.fromParts (source,provenance.immutable,provenance.sharedRef)).mapError reprStr
    let pointers ← allocation.provenanceMap.ptrs.mapM fun (offset,provenance) => do
      pure (offset,← convert provenance)
    let fragments ← allocation.provenanceMap.byteFragments.mapM fun fragments => fragments.mapM fun (offset,fragment) => do
      pure (offset,{fragment with prov := ← convert fragment.prov})
    (ProvenanceMap.fromParts pointers fragments).mapError reprStr
  let rawProvenance ← match rawResult with
    | .error error => return (.error error,world)
    | .ok value => pure value
  let key : MemoryKey := {
    bytes := bytes
    initMask := allocation.initializationMask
    alignment := alignment
    mutable := false
    pointerBytes := (Size.fromBits target.pointerWidth.bits).bytes
    littleEndian := target.endian == .little
    provenance := rawProvenance}
  let (reserved,world) := reserve run world
  let id ← match reserved with | .error error => return (.error error,world) | .ok id => pure id
  let global : GlobalAllocation := ⟨id,.memory,allocation.byteSize,allocation.align,.Not,some (.memory allocation)⟩
  return (.ok id,{world with memory := world.memory.pushGlobal global,symbolic := world.symbolic.push (id,.memory key)})
/-- Exact Action adapter. The owner supplies diagnostic classification; no
counter successor is thrown away when the underlying operation fails. -/
def asAction {D A : Type} (report : String → CtfeQueryBridge.Failure D)
    (operation : AllocatorWorld P E K → Except String A × AllocatorWorld P E K) :
    CtfeQueryBridge.Action (AllocatorWorld P E K) D A := fun world =>
  let (result,world) := operation world
  (result.mapError report,world)

end Miri.Input.CompilerInitialAllocation.VTableActions
