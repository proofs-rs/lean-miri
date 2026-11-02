import empty_function.Target
import empty_function.AllocatorActive
import empty_function.TreeRuntimeInput
import empty_function.ExternMapping

/-! Data-only input draft for review. This is NOT an adopted complete validity
definition. The remaining metadata normalization and address/descriptor adequacy
questions are documented beside the relevant fields; there is no success,
trace, later-state capability or safety premise. -/
namespace EmptyFunction.InputDraft
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.TreeBorrows
open WholeCall
set_option autoImplicit false

abbrev Entry := LocalAllocation Provenance BorrowTree MiriMemoryKind
abbrev F := Frame Provenance LocalLayout MachineHooks.FrameExtra

/-- Pure current allocation-registry classification, including non-data and
dead metadata. Live/global entries need not be mutable for a zero-byte write. -/
inductive MetadataBacking (before : State) (id : AllocId) : Prop where
  | live (entry : Entry)
      (row : before.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
  | global (entry : GlobalAllocation)
      (row : before.machine.memory.findGlobal? id = some entry)
      (identity : entry.allocId = id)
  | extraFunction (row : before.machine.memory.hasExtraFunctionId id = true)
  | vaList (row : before.machine.memory.hasVaListId id = true)
  | dead (entry : DeadAllocation)
      (row : before.machine.memory.dead.find? (fun row => row.allocId == id) = some entry)

/-- Current address-table coherence. Freed allocations may retain base-cache
rows and share old addresses with later allocations; only current live IDs
must agree with the inverse table. Inverse keys themselves are strictly ordered
and contain live nonzero entries, as required by the source binary search. -/
structure AddressTables (before : State) : Prop where
  baseIds : (before.machine.user.addresses.baseAddr.toList.map (·.allocId)).Nodup
  inverseIds : (before.machine.user.addresses.intToPtrMap.toList.map (·.allocId)).Nodup
  suppliers : ∀ row ∈ before.machine.user.addresses.intToPtrMap,
    MetadataBacking before row.allocId
  inverseLive : ∀ row ∈ before.machine.user.addresses.intToPtrMap,
    before.machine.memory.isAllocLive row.allocId = true
  nonzero : ∀ row ∈ before.machine.user.addresses.intToPtrMap, row.address ≠ 0
  bases : ∀ row ∈ before.machine.user.addresses.intToPtrMap,
    before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == row.allocId) =
      some ⟨row.allocId, row.address⟩
  liveBases : ∀ row ∈ before.machine.user.addresses.baseAddr,
    before.machine.memory.isAllocLive row.allocId = true → row.address ≠ 0 →
    ∃ inverse ∈ before.machine.user.addresses.intToPtrMap,
      inverse.allocId = row.allocId ∧ inverse.address = row.address
  ordered : before.machine.user.addresses.intToPtrMap.toList.Pairwise
    (fun left right => left.address < right.address)
  separated : ∀ left ∈ before.machine.user.addresses.intToPtrMap,
    ∀ right ∈ before.machine.user.addresses.intToPtrMap, left.allocId ≠ right.allocId →
    ∀ leftInfo rightInfo,
    before.machine.memory.getAllocInfo left.allocId = .ok leftInfo →
    before.machine.memory.getAllocInfo right.allocId = .ok rightInfo →
    left.address.toNat + max leftInfo.size.bytes.toNat 1 ≤ right.address.toNat ∨
      right.address.toNat + max rightInfo.size.bytes.toNat 1 ≤ left.address.toNat
  exposedLive : ∀ id ∈ before.machine.user.addresses.exposed,
    before.machine.memory.isAllocLive id = true
  exposedBases : ∀ id ∈ before.machine.user.addresses.exposed,
    ∃ base, before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id,base⟩

/-- Representation, distinct from numeric headroom. This record is required
only for a conversion branch that needs an uncached managed target address;
it does not require relocation targets to have cached bases or roots.
The pure allocation-size lookup describes current metadata, not allocation
materialization success. Dead base-cache rows impose no uniqueness of addresses. -/
structure GenerationRepresentation (before : State)
    (generation : AllocAddresses.AddressGenerationState) : Prop where
  current : before.machine.user.addresses.generation = some generation
  managed : before.machine.user.addresses.addressMode = .managed
  tables : AddressTables before
  reuseRateLower : Float.le 0.0 generation.reusePool.addressReuseRate = true
  reuseRateUpper : Float.le generation.reusePool.addressReuseRate 1.0 = true
  crossRateLower : Float.le 0.0 generation.reusePool.addressReuseCrossThreadRate = true
  crossRateUpper : Float.le generation.reusePool.addressReuseCrossThreadRate 1.0 = true
  poolKeys : ∀ bucket ∈ generation.reusePool.pool,
    bucket.toList.Pairwise (fun left right =>
      left.size.bytes < right.size.bytes ∨
        (left.size = right.size ∧ left.thread ≤ right.thread))
  poolSize : ∀ bucket ∈ generation.reusePool.pool, bucket.size ≤ AllocAddresses.maxReusePoolSize
  poolAddresses : ∀ bucket ∈ generation.reusePool.pool,
    ∀ entry ∈ bucket, entry.address ≠ 0 ∧
      entry.address.toNat + max entry.size.bytes.toNat 1 ≤ generation.generator.nextBaseAddr.toNat
  poolAlignment : ∀ index (valid : index < generation.reusePool.pool.size),
    ∀ entry ∈ generation.reusePool.pool[index], entry.address.toNat % (2^index) = 0
  poolUnique : ((generation.reusePool.pool.toList.flatMap Array.toList).map (·.address)).Nodup
  poolSeparatedPairwise : (generation.reusePool.pool.toList.flatMap Array.toList).Pairwise
    (fun left right =>
      left.address.toNat + max left.size.bytes.toNat 1 ≤ right.address.toNat ∨
        right.address.toNat + max right.size.bytes.toNat 1 ≤ left.address.toNat)
  poolAbsent : ∀ bucket ∈ generation.reusePool.pool, ∀ entry ∈ bucket,
    ∀ row ∈ before.machine.user.addresses.intToPtrMap, entry.address ≠ row.address
  poolSeparated : ∀ bucket ∈ generation.reusePool.pool, ∀ entry ∈ bucket,
    ∀ row ∈ before.machine.user.addresses.intToPtrMap,
    ∀ info, before.machine.memory.getAllocInfo row.allocId = .ok info →
    entry.address.toNat + max entry.size.bytes.toNat 1 ≤ row.address.toNat ∨
      row.address.toNat + max info.size.bytes.toNat 1 ≤ entry.address.toNat
  allocatedBeforeCursor : ∀ row ∈ before.machine.user.addresses.intToPtrMap,
    ∀ info, before.machine.memory.getAllocInfo row.allocId = .ok info →
      row.address.toNat + max info.size.bytes.toNat 1 ≤ generation.generator.nextBaseAddr.toNat

/-- Initial numeric conversion reserve. Charge each possible miss, including
alignment/slack arithmetic intermediates; no future callback outcome occurs.
The caller supplies bounds for the actual finite target metadata separately. -/
structure GenerationResources (generation : AllocAddresses.AddressGenerationState)
    (misses maximumSize maximumAlignment : Nat) : Prop where
  positiveCursor : 0 < generation.generator.nextBaseAddr.toNat
  cursorBeforeEnd : generation.generator.nextBaseAddr ≤ generation.generator.endAddr
  arithmetic : generation.generator.nextBaseAddr.toNat +
    misses * (15 + maximumAlignment + max maximumSize 1) < 2^64
  capacity : generation.generator.nextBaseAddr.toNat +
    misses * (15 + maximumAlignment + max maximumSize 1) ≤ generation.generator.endAddr.toNat

/-- Supported layout arithmetic is a pure fact about current compiler data,
not a success condition for address generation. -/
def AlignmentRepresentation (align : Align) : Prop :=
  ∃ bytes, Align.bytes align = .ok bytes ∧ Align.fromBytes bytes = .ok align

/-- Actual CTFE storage, with arbitrary finite pointer relocations retained.
No initialization is required just to inspect/materialize raw compiler bytes. -/
structure CompilerAllocation (source : Allocation CtfeProvenance Unit) : Prop where
  storage : source.len = source.byteSize.bytes.toNat
  mask : source.initializationMask.len = source.byteSize
  alignment : AlignmentRepresentation source.align
  fragments : source.provenanceMap.byteFragments = none
  windows : ∀ row ∈ source.provenanceMap.ptrs,
    row.1.bytes.toNat + 8 ≤ source.len
  ordered : source.provenanceMap.ptrs.toList.Pairwise
    (fun left right => left.1.bytes.toNat + 8 ≤ right.1.bytes.toNat)

/-- Resolve a raw CTFE declaration to its actual backing identity using
pure shim/weak/exported-winner metadata. Resource and address conditions apply
to that resolved ID. Runtime external/TLS pointers already carry their storage
ID; a direct TLS declaration is not a valid CTFE relocation representation. -/
structure RelocationTarget (s : Static) (before : State) (declared : AllocId) where
  resolved : AllocId
  mapping : ExternMapping.Target s before declared resolved
  backing : MetadataBacking before resolved
  live : before.machine.memory.isAllocLive resolved = true
  uncachedAlignment :
    (before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == resolved)) = none →
    ∀ info, before.machine.memory.getAllocInfo resolved = .ok info →
      AlignmentRepresentation info.align

/-- Source-specific metadata admits arbitrary finite relocations. A missing
base of the actual resolved target requires generation representation; no root
or address allocation is assumed to succeed. Shim/weak runtime pointers carry
existing current bases, while an exported winner may need a fresh base. -/
structure RelocationInput (s : Static) (before : State)
    (source : Allocation CtfeProvenance Unit) : Prop where
  physical : CompilerAllocation source
  targets : ∀ row ∈ source.provenanceMap.ptrs,
    Nonempty (RelocationTarget s before row.2.allocId)
  generation :
    (∃ row ∈ source.provenanceMap.ptrs, ∃ target : RelocationTarget s before row.2.allocId,
      (before.machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == target.resolved)) = none ∧
      ∃ info, before.machine.memory.getAllocInfo target.resolved = .ok info ∧ info.kind ≠ .typeId) →
    ∃ current, GenerationRepresentation before current

/-- The exact current descriptor payload is associated with its own physical
source. Internal static contents come from the actual imported initializer.
External/TLS descriptors stay explicit unfinished branches; they are not erased
from input coverage or treated as successful internal materialization. -/
inductive GlobalContent (s : Static) (before : State) (global : GlobalAllocation) : Prop where
  | memory (source : Allocation CtfeProvenance Unit)
      (kind : global.kind = .memory) (payload : global.payload = some (.memory source))
      (size : global.size = source.byteSize) (align : global.align = source.align)
      (mutability : global.mutability = source.mutability)
      (sourceInput : RelocationInput s before source)
  | internalStatic (definition : Nat) (source : Allocation CtfeProvenance Unit)
      (kind : global.kind = .static)
      (payload : global.payload = some (.static definition true false false))
      (initializer : s.prepared.image.initializers.find? (·.1 == definition) = some (definition,source))
      (size : global.size = source.byteSize) (align : global.align = source.align)
      (mutability : global.mutability = source.mutability)
      (sourceInput : RelocationInput s before source)
  | externalStatic (definition : Nat)
      (kind : global.kind = .static)
      (payload : global.payload = some (.static definition true false true))
  | threadLocalStatic (definition : Nat) (foreign : Bool)
      (kind : global.kind = .static)
      (payload : global.payload = some (.static definition true true foreign))
  | function (kind : global.kind = .function)
  | vtable (kind : global.kind = .vtable)
  | typeId (kind : global.kind = .typeId)

/-- Strong backing classification only for a selected actual runtime pointer.
Foreign/TLS declaration IDs are compiler names, not its backing storage: those
runtime pointers use their resolved/live storage ID. The raw declaration rows
remain admitted as GlobalContent and foreign CTFE targets use ExternMapping.
Dead classification respects the actual metadata lookup precedence.
Inverse-table supplier metadata does not force unrelated descriptor contents
through conversion or restrict their relocation lists. -/
inductive Backing (s : Static) (before : State) (id : AllocId) : Prop where
  | live (entry : Entry)
      (row : before.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
  | global (entry : GlobalAllocation)
      (row : before.machine.memory.findGlobal? id = some entry)
      (identity : entry.allocId = id) (content : GlobalContent s before entry)
      (runtimeStorage : ∀ definition isStatic tls foreign,
        entry.payload = some (.static definition isStatic tls foreign) →
        tls = false ∧ foreign = false)
      (registryVacant : before.machine.memory.live.find? (fun row => row.1 == id) = none →
        (entry.kind = .memory ∨ entry.kind = .static) →
        (before.machine.user.payload.payload.user.runtime.extras.allocations.any
          (fun row => row.1 == id)) = false)
  | extraFunction (row : before.machine.memory.hasExtraFunctionId id = true)
  | vaList (row : before.machine.memory.hasVaListId id = true)
  | dead (entry : DeadAllocation)
      (row : before.machine.memory.dead.find? (fun row => row.allocId == id) = some entry)
      (noLive : before.machine.memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : before.machine.memory.hasFunctionPointer id = false)
      (noVaList : before.machine.memory.hasVaListId id = false)
      (noGlobal : before.machine.memory.findGlobal? id = none)

/-- Raw zero-size inverse-search candidate. This is nearest-key geometry and
metadata size, not a premise that the operational resolver succeeds. -/
def WildcardCandidate (before : State) (pointer : Pointer (Option Provenance))
    (row : AllocAddresses.InverseAddressEntry) : Prop :=
  row.address ≤ pointer.offset.bytes ∧
  (∀ later ∈ before.machine.user.addresses.intToPtrMap,
    row.address < later.address → pointer.offset.bytes < later.address) ∧
  (pointer.offset.bytes = row.address ∨ ∃ info,
    before.machine.memory.getAllocInfo row.allocId = .ok info ∧
    pointer.offset.bytes.toNat < row.address.toNat + info.size.bytes.toNat)

/-- Provenance alternatives. No nonnull, byte-bounds, initialization or
mutability condition is imposed on a unit memory pointer. Concrete live values
bind the actual parent tag; concrete latent data binds its existing source root, a pointer-specific
current provenance coherence condition (not a cached-target restriction).
Wildcard pointers allow both hit and miss, including uncached latent roots. -/
inductive PointerInput (s : Static) (before : State) (tracker : MachineHooks.BorrowState)
    (pointer : Pointer (Option Provenance)) : Prop where
  | integer (encoding : pointer.provenance = none)
  | concrete (id : AllocId) (tag : BorTag) (base : UInt64)
      (tables : AddressTables before)
      (encoding : pointer.provenance = some (.concrete id tag))
      (cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
        some ⟨id, base⟩)
      (backing : Backing s before id)
      (parent : ∀ entry : Entry,
        before.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry) →
        ∃ index node, entry.allocation.extra.tagMapping.get tag = some index ∧
          entry.allocation.extra.nodes.get index = some node ∧ node.tag = tag)
      (latentRoot : before.machine.memory.live.find? (fun row => row.1 == id) = none →
        ∀ global, before.machine.memory.findGlobal? id = some global →
        (global.kind = .memory ∨ global.kind = .static) →
        tracker.global.rootTag? id = some tag)
  | wildcard (encoding : pointer.provenance = some .wildcard)
      (mode : before.machine.user.addresses.provenanceMode ≠ .strict)
      (tables : AddressTables before)
      (selected : ∀ row ∈ before.machine.user.addresses.intToPtrMap,
        before.machine.user.addresses.exposed.contains row.allocId = true →
        WildcardCandidate before pointer row → Backing s before row.allocId)

/-- Pure compiler binding for an arbitrary current caller, including generic
local normalization. Neither query executes a memory/call/retag operation. -/
structure LocalMetadata (s : Static) (caller : F) (id : LocalId) (layout : LocalLayout) where
  normalizedTy : TyId
  normalization : Input.CompilerFrameContext.normalizedLocalType s.prepared.compiler caller id = .ok normalizedTy
  lookup : s.prepared.compiler.runtime.lookup normalizedTy = .ok layout

/-- Raw extent of an existing nonzero enclosing local's indirect backing.
The wildcard attribution is expressed with current inverse rows and addresses,
not with a successful resolver call. Zero-sized parents need no such backing. -/
structure IndirectFootprint (before : State) (pointer : Pointer (Option Provenance))
    (length : Size) where
  id : AllocId
  entry : Entry
  live : before.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry)
  base : UInt64
  relative : UInt64
  cached : before.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩
  address : pointer.offset.bytes.toNat = base.toNat + relative.toNat
  addressFits : base.toNat + entry.allocation.byteSize.bytes.toNat < 2^64
  extent : relative.toNat + length.bytes.toNat ≤ entry.allocation.byteSize.bytes.toNat
  attribution : match pointer.provenance with
    | none => False
    | some (.concrete supplied _) => supplied = id
    | some .wildcard =>
      before.machine.user.addresses.provenanceMode ≠ .strict ∧
      before.machine.user.addresses.exposed.contains id = true ∧
      (∃ row ∈ before.machine.user.addresses.intToPtrMap, row.allocId = id ∧ row.address = base) ∧
      (∀ row ∈ before.machine.user.addresses.intToPtrMap,
        row.address ≤ pointer.offset.bytes → row.address ≤ base)

/-- Public scalar constructors preserve their payload width and normalization.
ScalarInt construction checks a nonzero 1–16 byte width and truncates the bits;
Scalar.fromPointer installs the current target's pointer width. These raw
normal forms add no bool, char, reference or other typed-value validity test. -/
inductive RawCanonicalScalar (target : TargetDataLayout) (value : Scalar Provenance) : Prop where
  | integer (payload : ScalarInt) (encoding : value = Scalar.fromScalarInt payload)
      (nonzero : payload.size.bytes ≠ 0) (width : payload.size.bytes.toNat ≤ 16)
      (truncated : payload.toBitsUnchecked.toNat < 2^(payload.size.bytes.toNat*8))
  | pointer (pointer : Pointer Provenance) (encoding : value = Scalar.fromPointer target pointer)

/-- Current scalar encoding agrees with its ABI primitive width and pointer
category. This is a pure representation predicate, not a write-success law. -/
def ScalarEncoding (runtime : RuntimeTargetDataLayout) (primitive : BackendPrimitive)
    (value : Scalar Provenance) : Prop :=
  RawCanonicalScalar runtime.base value ∧
  ∃ size, Primitive.size primitive runtime = .ok size ∧ value.size = size ∧
    (match primitive with | .Pointer _ => True | _ => value.isPointer = false)

def ImmediateEncoding (runtime : RuntimeTargetDataLayout) (layout : LocalLayout)
    (value : Immediate Provenance) : Prop :=
  match value, layout.layout.backendRepr with
  | .uninit, _ => layout.layout.isSized = true
  | .scalar value, .Scalar abi =>
    ScalarEncoding runtime abi.primitive value ∧ value.size.bytes ≤ layout.layout.size.bytes
  | .scalarPair first second, .ScalarPair (a := a) (b := b) (bOffset := offset) =>
    ScalarEncoding runtime a.primitive first ∧ ScalarEncoding runtime b.primitive second ∧
      offset.bytes ≠ 0 ∧ first.size.bytes ≤ offset.bytes ∧
      offset.bytes.toNat + second.size.bytes.toNat ≤ layout.layout.size.bytes.toNat
  | _, _ => False

/-- Initial whole/projected local representation, before reading it. -/
structure LocalDestination (s : Static) (p : Packet)
    (tracker : MachineHooks.BorrowState) where
  caller : F
  current : p.before.stack.currentFrame? = some caller
  localId : LocalId
  offset : Option Size
  baseLayout : LocalLayout
  slot : LocalState Provenance LocalLayout
  slotAt : caller.locals[localId]? = some slot
  metadata : LocalMetadata s caller localId baseLayout
  cache : slot.layout = none ∨ slot.layout = some baseLayout
  baseSized : baseLayout.layout.isSized = true
  baseSigned : baseLayout.layout.size.bytes.toNat < 2^63
  oldOperand : Operand Provenance
  live : slot.value = .live oldOperand
  oldEncoding : ∀ value, oldOperand = .immediate value →
    ImmediateEncoding s.prepared.compiler.runtime.target baseLayout value
  oldPointer : ∀ place, oldOperand = .indirect place → PointerInput s p.before tracker place.ptr
  oldRepresentation : ∀ place, oldOperand = .indirect place →
    place.metadata = .none ∧ place.misaligned = none
  oldFootprint : offset.isSome = true → baseLayout.layout.size.bytes ≠ 0 →
    ∀ place, oldOperand = .indirect place → Nonempty (IndirectFootprint p.before place.ptr baseLayout.layout.size)
  projection : match offset with
    | none => baseLayout = s.abi.ret.layout
    | some bytes => bytes.bytes.toNat ≤ baseLayout.layout.size.bytes.toNat
  encoding : p.destination = .frameLocal (p.before.stack.frames.size - 1)
    localId offset s.abi.ret.layout caller.localsIdentity

/-- Current memory destination; lazy descriptors and arbitrary relocation lists
are deliberately retained by Backing.global. Their raw metadata/format/address
adequacy conditions are still OPEN and must be specified without future ensure
or copy success. This draft does not assert their sufficiency. -/
structure MemoryDestination (s : Static) (p : Packet)
    (tracker : MachineHooks.BorrowState) where
  place : MPlaceTy Provenance
  encoding : p.destination = .memory place
  layout : place.layout = s.abi.ret.layout
  sizedMetadata : place.mplace.metadata = .none
  alignmentCache : place.mplace.misaligned = none
  pointer : PointerInput s p.before tracker place.mplace.ptr

/-- Exactly the current representation branch that forces allocation of an
enclosing optimized local during the projected unit return write. -/
def NeedsEnclosingAllocation (p : Packet) : Prop :=
  ∃ frame index localId offset layout identity slot value,
    p.before.stack.currentFrame? = some frame ∧
    p.destination = .frameLocal index localId (some offset) layout identity ∧
    frame.locals[localId]? = some slot ∧ slot.value = .live (.immediate value)

/-- Raw pointer denoted by the evaluated unit return place on the selected
64-bit target. A projected zero-sized field can resolve to a different exposed
allocation at an adjacent boundary; admission therefore classifies this pointer
as well as the original enclosing backing. This computes no memory operation. -/
def effectivePointer (p : Packet) : Option (Pointer (Option Provenance)) :=
  match p.destination with
  | .memory place => some place.mplace.ptr
  | .frameLocal _ localId offset _ _ => do
    let frame ← p.before.stack.currentFrame?
    let slot ← frame.locals[localId]?
    match slot.value with
    | .live (.indirect place) =>
      pure (match offset with
        | none => place.ptr
        | some bytes => {place.ptr with offset := Size.ofBytes (place.ptr.offset.bytes + bytes.bytes)})
    | .dead | .live (.immediate _) => none

/-- Raw allocator high-water bookkeeping for a branch creating fresh backing.
It is independent of whether any allocation operation will succeed. -/
structure AllocatorRepresentation (before : State) : Prop where
  /-- Cached keys are runtime AllocIds from this allocator's issued ledger,
  including retained freed-allocation rows. These are not CTFE source raw IDs. -/
  basesIssued : ∀ row ∈ before.machine.user.addresses.baseAddr,
    row.allocId ∈ before.machine.memory.issuedIds
  issued : ∀ id ∈ before.machine.memory.issuedIds,
    id.value.toNat < before.machine.memory.nextAllocId.toNat
  live : ∀ row ∈ before.machine.memory.live,
    row.1.value.toNat < before.machine.memory.nextAllocId.toNat
  global : ∀ row ∈ before.machine.memory.globals,
    row.allocId.value.toNat < before.machine.memory.nextAllocId.toNat
  dead : ∀ row ∈ before.machine.memory.dead,
    row.allocId.value.toNat < before.machine.memory.nextAllocId.toNat
  functions : ∀ id ∈ before.machine.memory.extraFnPtrIds,
    id.value.toNat < before.machine.memory.nextAllocId.toNat
  vaLists : ∀ id ∈ before.machine.memory.vaListIds,
    id.value.toNat < before.machine.memory.nextAllocId.toNat
  sourceIds : before.machine.memory.sourceAllocIdWorldActive = true →
    ∀ row ∈ before.machine.memory.sourceAllocIdByRuntime,
      row.2.toNat < before.machine.memory.sourceAllocIdNext.toNat

  /-- InitialMachine starts with no extras. Allocation reserves its runtime ID
  before MemoryExtras.initAllocation; updates use existing IDs and GC only
  removes rows. Retained extras therefore refer to the issued-ID ledger. -/
  extrasIssued : ∀ row ∈ before.machine.user.payload.payload.user.runtime.extras.allocations,
    row.1 ∈ before.machine.memory.issuedIds

/-- The allocator can proceed past its actual early exhaustion guards. This
is a classification of the current flags, not a resource margin. Wrapped or
exhausted supplies remain valid callers and stop safely before fresh backing. -/
def AllocatorActive (before : State) : Prop := EmptyFunction.AllocatorActive.Active before.machine.memory

/-- Initial-data candidate, intentionally named Draft rather than ValidInput.
Unrelated caller frames, memory and other threads may be arbitrary. Additional
ordinary runtime-map invariants and latent conversion metadata are unresolved.
The candidate cannot yet instantiate the public Target as a completed theorem. -/
structure CurrentInputDraft (s : Static) (p : Packet) where
  caller : F
  current : p.before.stack.currentFrame? = some caller
  callerMir : ∃ location, caller.location = .mir location
  callerNoClocks : caller.extra.dataRace = none
  continuation : p.returnBlock < caller.body.basicBlocks.size
  thread : Concurrency.ThreadRecord
  active : p.before.machine.threads.activeThread? = some thread
  relevance : ∀ index, thread.topUserRelevantFrame = some index → index < p.before.stack.frames.size
  tracker : MachineHooks.BorrowState
  world : TreeRuntimeInput.World p.before.machine tracker
  effective : ∀ pointer, effectivePointer p = some pointer → PointerInput s p.before tracker pointer
  projectedGeneration : NeedsEnclosingAllocation p → AllocatorActive p.before →
    ∃ generation, GenerationRepresentation p.before generation
  projectedAllocator : NeedsEnclosingAllocation p → AllocatorActive p.before → AllocatorRepresentation p.before
  destination : Nonempty (LocalDestination s p tracker) ∨ Nonempty (MemoryDestination s p tracker)

end EmptyFunction.InputDraft
