import duplicate_prefix.WildcardEmptyCoherentResolution
import duplicate_prefix.ConcreteEmptyReferenceBorrow
import duplicate_prefix.GlobalSupportedImage

/-! Raw empty-reference authorization candidate. No field assumes a successful
lookup, retag, call, or execution history. This deliberately normalized first
interface supports provenance-free dangling pointers, live concrete parents,
nondata/dead concrete metadata, and coherent nonstrict wildcard searches.
Lazy MEMORY/STATIC targets additionally require source images, initializer
metadata, supported relocations, cached root tags and absent runtime extras.
The enclosing specification must bind ImageContext to actual compiler/state
fields; it must not existentially choose a convenient context.
Full ordinary-valid-input coverage and actual-call safety remain unproved.
-/
namespace DuplicatePrefix.DuplicatePrefixEmptyReferenceInput
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open Miri.TreeBorrows Miri.Interpreter Miri.Input

set_option autoImplicit false in
/-- A concrete parent is actually mapped and present. Wildcard child creation
has no concrete parent and therefore needs no invented parent tag. -/
def Parent (tree : BorrowTree) (tag : Option BorTag) : Prop :=
  match tag with
  | none => True
  | some tag => ∃ index node, tree.indexOfTag tag = some index ∧ tree.nodeAt index = some node

set_option autoImplicit false in
/-- Source-precedence metadata suppliers, with the extra parent condition only
for an already-live concrete tree. Nondata and dead rows return before the
live-tree child insertion. Lazy live-data globals need a future separate image
contract and are not accepted by the nondata constructor. -/
inductive Metadata {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (tag : Option BorTag) : Prop where
  | live (entry : LocalAllocation Provenance BorrowTree K)
      (present : memory.live.find? (fun row => row.1 == id) = some (id, entry))
      (parent : Parent entry.allocation.extra tag)
  | functionRow (absent : memory.live.find? (fun row => row.1 == id) = none)
      (present : memory.hasFunctionPointer id = true)
  | vaListRow (absent : memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : memory.hasFunctionPointer id = false)
      (present : memory.hasVaListId id = true)
  | nondataGlobal (descriptor : GlobalAllocation)
      (absent : memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : memory.hasFunctionPointer id = false)
      (noVaList : memory.hasVaListId id = false)
      (present : memory.findGlobal? id = some descriptor)
      (kind : descriptor.kind = .function ∨ descriptor.kind = .vtable ∨ descriptor.kind = .typeId)
  | dead (entry : DeadAllocation)
      (absent : memory.live.find? (fun row => row.1 == id) = none)
      (noFunction : memory.hasFunctionPointer id = false)
      (noVaList : memory.hasVaListId id = false)
      (noGlobal : memory.findGlobal? id = none)
      (present : memory.dead.find? (fun row => row.allocId == id) = some entry)

/-- Successful metadata lookup is a derived fact, not a contract field. -/
theorem metadata_known {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (tag : Option BorTag) (input : Metadata memory id tag) :
    ∃ info, memory.getAllocInfo id = .ok info := by
  cases input with
  | live entry present parent =>
    exact ⟨_, by simp only [MemoryState.getAllocInfo, present]; rfl⟩
  | functionRow absent present =>
    exact ⟨_, by simp only [MemoryState.getAllocInfo, absent, present, ↓reduceIte]; rfl⟩
  | vaListRow absent noFunction present =>
    unfold MemoryState.hasVaListId at present
    exact ⟨_, by simp only [MemoryState.getAllocInfo, absent, noFunction, present,
      Bool.false_eq_true, ↓reduceIte]; rfl⟩
  | nondataGlobal descriptor absent noFunction noVaList present kind =>
    unfold MemoryState.hasVaListId at noVaList
    simp only [MemoryState.getAllocInfo, absent, noFunction, noVaList, present,
      Bool.false_eq_true, ↓reduceIte]
    cases descriptor.kind <;> exact ⟨_, rfl⟩
  | dead entry absent noFunction noVaList noGlobal present =>
    unfold MemoryState.hasVaListId at noVaList
    exact ⟨_, by simp only [MemoryState.getAllocInfo, absent, noFunction, noVaList,
      noGlobal, present, Bool.false_eq_true, ↓reduceIte]; rfl⟩

set_option autoImplicit false in
/-- Raw projections to be constructed from the actual compiler image, tracker,
runtime extras and native-library configuration. This is data, not an opaque
materialization-success assumption. The caller must bind every field to its
actual source; an existentially chosen context would not be sound wiring. -/
structure ImageContext where
  runtime : RuntimeTargetDataLayout
  initializers : Array (Nat × Allocation CtfeProvenance Unit)
  rootTags : Array (AllocId × BorTag)
  extraAllocationIds : Array AllocId
  nativeLibraryPathsEmpty : Bool

set_option autoImplicit false in
/-- Actual exported MEMORY or non-TLS, non-extern STATIC initializer shape. -/
def ImageDescriptor {K : Type} (context : ImageContext)
    (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (source : Allocation CtfeProvenance Unit) : Prop :=
  memory.findGlobal? id = some
    ⟨id, .memory, source.byteSize, source.align, source.mutability, some (.memory source)⟩ ∨
  ∃ definition,
    context.initializers.find? (·.1 == definition) = some (definition, source) ∧
    memory.findGlobal? id = some
      ⟨id, .static, source.byteSize, source.align, source.mutability,
        some (.static definition true false false)⟩

set_option autoImplicit false in
/-- Conservative lazy-global source candidate. A concrete incoming tag must be
exactly the cached root installed by materialization. Wildcard roots need no
incoming concrete tag. Freshness, graph/storage invariants and numeric bounds
remain separate runtime/resources obligations; actual-call sufficiency and
coverage of all valid images are not established by this definition. -/
def Materializable {K : Type} (context : ImageContext)
    (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (id : AllocId) (tag : Option BorTag) : Prop :=
  ∃ source root,
    memory.live.find? (fun row => row.1 == id) = none ∧
    memory.hasFunctionPointer id = false ∧ memory.hasVaListId id = false ∧
    ImageDescriptor context memory id source ∧
    (context.rootTags.find? (fun row => row.1 == id)).map Prod.snd = some root ∧
    (tag = none ∨ tag = some root) ∧
    context.extraAllocationIds.contains id = false ∧
    context.nativeLibraryPathsEmpty = true ∧
    GlobalSupportedImage.Supported source context.runtime memory context.rootTags addresses.baseAddr

set_option autoImplicit false in
def TargetMetadata {K : Type} (context : ImageContext)
    (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (id : AllocId) (tag : Option BorTag) : Prop :=
  Metadata memory id tag ∨ Materializable context memory addresses id tag

theorem target_metadata_known {K : Type} (context : ImageContext)
    (memory : MemoryState Provenance BorrowTree K) (addresses : GlobalAddressState)
    (id : AllocId) (tag : Option BorTag)
    (input : TargetMetadata context memory addresses id tag) :
    ∃ info, memory.getAllocInfo id = .ok info := by
  rcases input with known | ⟨source, root, absent, noFunction, noVaList, descriptor, rest⟩
  · exact metadata_known memory id tag known
  · unfold MemoryState.hasVaListId at noVaList
    rcases descriptor with descriptor | ⟨definition, initializer, descriptor⟩
    all_goals exact ⟨_, by simp only [MemoryState.getAllocInfo, absent, noFunction,
      noVaList, descriptor, Bool.false_eq_true, ↓reduceIte]; rfl⟩

set_option autoImplicit false in
/-- Cached concrete conversion plus actual metadata. No in-bounds byte or live
backing is demanded of a nonlive zero-byte reference. -/
def Concrete {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (id : AllocId) (tag : BorTag) : Prop :=
  (∃ base, addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩) ∧
    TargetMetadata context memory addresses id (some tag)

set_option autoImplicit false in
/-- Raw finite map consistency handles both exact hits and predecessor/gap
queries. Exposed potential targets have cached bases and supported metadata;
unexposed rows still supply size metadata. Requiring this for every indexed
row is conservative: only the selected exact/predecessor row is queried.
No resolved allocation or successful resolver equation is assumed. -/
structure Wildcard {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) : Prop where
  nonstrict : addresses.provenanceMode ≠ .strict
  coherent : GlobalAddressRecurringFormation.State memory addresses
  sizes : ∀ row ∈ addresses.intToPtrMap,
    GlobalAddressLiveErrorExclusion.Supplier memory row.allocId
  cached : ∀ row ∈ addresses.intToPtrMap, addresses.exposed.contains row.allocId = true →
    addresses.baseAddr.find? (fun entry => entry.allocId == row.allocId) = some ⟨row.allocId, row.address⟩
  targets : ∀ row ∈ addresses.intToPtrMap, addresses.exposed.contains row.allocId = true →
    TargetMetadata context memory addresses row.allocId none

/-- The initial wildcard size/liveness lookup completes from raw suppliers.
This does not prove later retagging or the function invocation. -/
theorem wildcard_lookup_total {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (input : Wildcard context memory addresses) (address : UInt64) :
    ∃ result, addresses.allocIdFromAddr address 0 (GlobalAddressLiveErrorExclusion.lookup memory) = .ok result :=
  WildcardEmptyCoherentResolution.total memory addresses address input.coherent input.nonstrict input.sizes

set_option autoImplicit false in
/-- Provenance-dependent empty-input candidate. Runtime forest, fresh-tag,
allocator, model, ABI and numeric-resource obligations belong to the enclosing
call specification. Integer/no-provenance values require only nonnull here;
in particular no live allocation is fabricated for a dangling empty slice. -/
def Candidate {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (pointer : Pointer (Option Provenance)) : Prop :=
  pointer.offset.bytes ≠ 0 ∧
    match pointer.provenance with
    | none => True
    | some (.concrete id tag) => Concrete context memory addresses id tag
    | some .wildcard => Wildcard context memory addresses

theorem no_provenance_iff {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64) :
    Candidate context memory addresses (Pointer.new none (Size.ofBytes address)) ↔ address ≠ 0 := by
  simp [Candidate, Pointer.new, Size.ofBytes]

theorem wildcard_nonstrict {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64)
    (input : Candidate context memory addresses (Pointer.new (some .wildcard) (Size.ofBytes address))) :
    addresses.provenanceMode ≠ .strict := input.2.nonstrict

theorem concrete_metadata_known {K : Type} (context : ImageContext) (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (address : UInt64) (id : AllocId) (tag : BorTag)
    (input : Candidate context memory addresses (Pointer.new (some (.concrete id tag)) (Size.ofBytes address))) :
    ∃ info, memory.getAllocInfo id = .ok info :=
  target_metadata_known context memory addresses id (some tag) input.2.2

end DuplicatePrefix.DuplicatePrefixEmptyReferenceInput
