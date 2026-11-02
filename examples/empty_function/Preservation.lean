import empty_function.Target
import empty_function.InputDraft

/-! Concrete observable caller-resource preservation proposed for the target.
New bookkeeping nodes/caches and backing for materialized caller locals may be
added. Every original live byte allocation and old node's permission/accessed
projection is retained. No theorem in this file asserts these obligations hold. -/
namespace EmptyFunction.Preservation
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open WholeCall
set_option autoImplicit false

def ContainsByte (segment : DataStructures.RangeMapSegment LocationTree) (byte : Nat) : Prop :=
  segment.range.start.toNat ≤ byte ∧ byte < segment.range.stop.toNat

def OldNodeRights (before after : BorrowTree) : Prop :=
  (∀ tag index, before.tagMapping.get tag = some index → after.tagMapping.get tag = some index) ∧
  (∀ root ∈ before.roots, root ∈ after.roots) ∧
  ∀ index old, before.nodes.get index = some old →
    ∃ current, after.nodes.get index = some current ∧
      current.tag = old.tag ∧ current.parent = old.parent ∧ current.isExposed = old.isExposed ∧
      current.defaultLocationState.permission = old.defaultLocationState.permission ∧
      current.defaultLocationState.accessed = old.defaultLocationState.accessed ∧
      (∀ child ∈ old.children, child ∈ current.children) ∧
      (∀ byte segment, segment ∈ before.locations.entries → ContainsByte segment byte →
        ∃ next, next ∈ after.locations.entries ∧ ContainsByte next byte ∧
          ((next.data.perms.get index).getD current.defaultLocationState).permission =
            ((segment.data.perms.get index).getD old.defaultLocationState).permission ∧
          ((next.data.perms.get index).getD current.defaultLocationState).accessed =
            ((segment.data.perms.get index).getD old.defaultLocationState).accessed)

def OriginalLiveAllocations (before after : State) : Prop :=
  ∀ id old,
    before.machine.memory.live.find? (fun row => row.1 == id) = some (id, old) →
    ∃ current, after.machine.memory.live.find? (fun row => row.1 == id) = some (id, current) ∧
      current.kind = old.kind ∧
      current.allocation.mapExtra (fun _ => ()) = old.allocation.mapExtra (fun _ => ()) ∧
      OldNodeRights old.allocation.extra current.allocation.extra

def ExistingProtectors (before after : State) : Prop :=
  ∀ old, before.machine.borrowTracker = some old →
    ∃ current, after.machine.borrowTracker = some current ∧
      current.global.protectedTags = old.global.protectedTags

def ExistingRoots (before after : State) : Prop :=
  ∀ old, before.machine.borrowTracker = some old →
    ∃ current, after.machine.borrowTracker = some current ∧
      ∀ id tag, old.global.rootTag? id = some tag → current.global.rootTag? id = some tag

def OtherThreads (before after : State) : Prop :=
  after.machine.threads.activeThread = before.machine.threads.activeThread ∧
  after.machine.threads.threads.length = before.machine.threads.threads.length ∧
  ∀ index, index ≠ before.machine.threads.activeThread.toNat →
    after.machine.threads.threads[index]? = before.machine.threads.threads[index]?

/-- Unrelated caller slots retain their value and cached layout. Only the
selected local may change representation for a local return destination. -/
def CallerSlots (p : Packet) (after : State) : Prop :=
  ∀ original caller,
    p.before.stack.currentFrame? = some original → after.stack.currentFrame? = some caller →
    caller.locals.size = original.locals.size ∧
    ∀ index,
      (match p.destination with
        | .memory _ => True
        | .frameLocal _ localId _ _ _ => index ≠ localId) →
      caller.locals[index]? = original.locals[index]?

/-- The caller's own return continuation, destination, argument metadata and
owned protectors survive. Its instruction location and selected local storage
are the only frame components allowed to change. -/
def CallerContext (p : Packet) (after : State) : Prop :=
  ∀ original caller,
    p.before.stack.currentFrame? = some original → after.stack.currentFrame? = some caller →
    {caller with location := original.location, locals := original.locals} = original

def eraseThreadRelevance (manager : Concurrency.ThreadManager) : Concurrency.ThreadManager :=
  {manager with threads := manager.threads.map (fun thread => {thread with topUserRelevantFrame := none})}

/-- Apart from the explicit active relevance cache, thread-manager state is
preserved. OtherThreads separately retains the caches of all other threads. -/
def ThreadContext (before after : State) : Prop :=
  eraseThreadRelevance after.machine.threads = eraseThreadRelevance before.machine.threads

def ExistingAddressFacts (before after : State) : Prop :=
  after.machine.user.addresses.addressMode = before.machine.user.addresses.addressMode ∧
  after.machine.user.addresses.provenanceMode = before.machine.user.addresses.provenanceMode ∧
  (∀ id row, before.machine.user.addresses.baseAddr.find? (fun old => old.allocId == id) = some row →
    after.machine.user.addresses.baseAddr.find? (fun current => current.allocId == id) = some row) ∧
  (∀ row ∈ before.machine.user.addresses.intToPtrMap,
    ∃ current ∈ after.machine.user.addresses.intToPtrMap,
      current.allocId = row.allocId ∧ current.address = row.address) ∧
  (∀ id ∈ before.machine.user.addresses.exposed,
    after.machine.user.addresses.exposed.contains id = true)

def RuntimeContext (before after : State) : Prop :=
  after.machine.user.payload.payload.user.types = before.machine.user.payload.payload.user.types ∧
  after.machine.user.payload.ghost = before.machine.user.payload.ghost ∧
  after.machine.user.payload.validation = before.machine.user.payload.validation ∧
  after.machine.user.payload.payload.user.host.ioSources = before.machine.user.payload.payload.user.host.ioSources ∧
  {after.machine.user.payload.payload.user.host.control with
    basicBlockCount := before.machine.user.payload.payload.user.host.control.basicBlockCount,
    sinceGc := before.machine.user.payload.payload.user.host.control.sinceGc,
    monotonic := before.machine.user.payload.payload.user.host.control.monotonic} =
      before.machine.user.payload.payload.user.host.control

private def writeImageScalar (target : TargetDataLayout) (allocation : Allocation Provenance Unit)
    (offset : Size) (value : Scalar Provenance) : Option (Allocation Provenance Unit) :=
  match Allocation.writeScalar target (allocRange offset value.size) value allocation with
  | .ok _ after => some after
  | .error _ _ => none

/-- Pure ABI storage image, without hooks, allocation identities or TB extras.
Uninitialized raw bytes are ignored by StorageImage below. -/
def expectedImage (target : TargetDataLayout) (layout : LocalLayout)
    (value : Immediate Provenance) : Option (Allocation Provenance Unit) := do
  let initialized ← (Allocation.fromBytes (Prov := Provenance)
    (Array.replicate layout.layout.size.bytes.toNat 0) layout.layout.align.abi .Mut).toOption
  let uninitialized ← match Allocation.writeUninit (allocRange Size.ZERO layout.layout.size)
      (Size.fromBits target.pointerWidth.bits) initialized with
    | .ok _ after => some after
    | .error _ _ => none
  match value with
  | .uninit => pure uninitialized
  | .scalar scalar => writeImageScalar target uninitialized Size.ZERO scalar
  | .scalarPair first second =>
    let .ScalarPair (bOffset := offset) .. := layout.layout.backendRepr | none
    let first ← writeImageScalar target uninitialized Size.ZERO first
    writeImageScalar target first offset second

def StorageImage (expected : Allocation Provenance Unit)
    (actual : Allocation Provenance BorrowTree) : Prop :=
  actual.byteSize = expected.byteSize ∧ actual.provenanceMap = expected.provenanceMap ∧
  ∀ byte, byte < expected.len →
    let range := allocRange (Size.ofBytes (UInt64.ofNat byte)) (Size.ofBytes 1)
    actual.initializationMask.isRangeInitialized range = expected.initializationMask.isRangeInitialized range ∧
    (expected.initializationMask.isRangeInitialized range = .ok (.ok ()) →
      actual.getBytesUnchecked range = expected.getBytesUnchecked range)

/-- A projected unit store preserves its enclosing local's prior storage image.
An already-indirect local keeps that place. An immediate local may acquire
fresh backing; its initialized contents and provenance must match the pure
encoding of the original immediate and normalized enclosing layout. -/
def SelectedProjectedContents (s : Static) (p : Packet) (after : State) : Prop :=
  match p.destination with
  | .memory _ | .frameLocal _ _ none _ _ => True
  | .frameLocal _ localId (some _) _ _ =>
    ∀ original caller old current,
      p.before.stack.currentFrame? = some original → after.stack.currentFrame? = some caller →
      original.locals[localId]? = some old → caller.locals[localId]? = some current →
      match old.value with
      | .dead => False
      | .live (.indirect memory) => current.value = .live (.indirect memory)
      | .live (.immediate value) =>
        ∃ layout, Nonempty (InputDraft.LocalMetadata s original localId layout) ∧
          ∃ memory id tag entry base expected,
            current.value = .live (.indirect memory) ∧
            memory.ptr.provenance = some (.concrete id tag) ∧
            after.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry) ∧
            after.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩ ∧
            memory.ptr.offset.bytes = base ∧
            expectedImage s.prepared.compiler.runtime.target.base layout value = some expected ∧
            StorageImage expected entry.allocation

/-- Whole-state equality is intentionally not required: actual zero protection
changes fresh-tag/node supplies and SIFA; a projected local may acquire backing.
The resumed caller identity/continuation/lower frames are specified by Returned.
Fresh address/root caches and counter/clock bookkeeping may grow, while their
existing observable entries and unrelated caller context are retained. -/
def Preserves (s : Static) (p : Packet) (after : State) : Prop :=
  Returned p after ∧ OriginalLiveAllocations p.before after ∧
    ExistingProtectors p.before after ∧ OtherThreads p.before after ∧ CallerSlots p after ∧
    SelectedProjectedContents s p after ∧ CallerContext p after ∧
    ThreadContext p.before after ∧ ExistingAddressFacts p.before after ∧ RuntimeContext p.before after ∧
    ExistingRoots p.before after

end EmptyFunction.Preservation
