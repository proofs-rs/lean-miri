import duplicate_prefix.GlobalAddressBaseCacheFormation

namespace DuplicatePrefix.OrdinaryAddressCachePreservation
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-- An optional stronger raw cache WF: each live allocation has an
identity-coherent base row. It is NOT claimed as necessary ordinary machine WF:
fresh live rows may precede their address acquisition. The preservation theorem
below keeps memory unchanged; selected call-pointer coverage can instead use
Retains on just its own cached allocation. This says nothing about borrow
permissions or whether allocation intervals are disjoint. -/
def LiveCached {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) : Prop :=
  ∀ row ∈ memory.live, ∃ base,
    addresses.baseAddr.find? (fun cached => cached.allocId == row.1) = some ⟨row.1, base⟩

/-- All old base lookups retain their exact addresses, not merely existence. -/
def Retains (before after : GlobalAddressState) : Prop :=
  ∀ id base, before.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩ →
    after.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩

theorem Retains.live_cached {K : Type} {memory : MemoryState Provenance BorrowTree K}
    {before after : GlobalAddressState} (retains : Retains before after)
    (wf : LiveCached memory before) : LiveCached memory after := by
  intro row member
  obtain ⟨base, found⟩ := wf row member
  exact ⟨base, retains row.1 base found⟩

/-- Actual registration cannot overwrite any existing base lookup. Existing
id registration returns its original state (and reports an error); a fresh id
insertion retains every other id by the existing insertion theorem. -/
theorem cache_retains (addresses : GlobalAddressState) (id : AllocId) (base : UInt64) :
    Retains addresses (addresses.cacheAddress id base).state := by
  intro query known cached
  cases found : addresses.baseAddr.find? (fun row => row.allocId == id) with
  | some row =>
    unfold GlobalAddressState.cacheAddress
    unfold_internal ".GlobalAddressState.findBase"
    simp only [found, Option.map_some]
    exact cached
  | none =>
    have different : query ≠ id := by intro same; subst query; rw [found] at cached; cases cached
    have keep := (GlobalAddressBaseCacheFormation.base_insert_other
      addresses.baseAddr id query base different).trans cached
    unfold GlobalAddressState.cacheAddress
    unfold_internal ".GlobalAddressState.findBase"
    unfold_internal ".GlobalAddressState.insertBase"
    simp only [found, Option.map_none]
    split
    · exact keep
    · split
      · split <;> exact keep
      · split <;> exact keep

private theorem returned_retains (before staged : GlobalAddressState)
    (retains : Retains before staged) (id : AllocId) (base : UInt64) :
    Retains before (match (staged.cacheAddress id base).outcome with
      | .ok _ => (show AddressStateResult AddressAssignment from
          ⟨(staged.cacheAddress id base).state, .ok (.ready base)⟩)
      | .error error => (show AddressStateResult AddressAssignment from
          ⟨(staged.cacheAddress id base).state, .error error⟩)).state := by
  cases (staged.cacheAddress id base).outcome <;>
    exact fun query known found => cache_retains staged id base query known (retains query known found)

/-- Full address-assignment preservation, uniformly over all choice inputs,
including legal existing/reuse/no-reuse/cross-thread branches and their actual
errors. No successful outcome or selected allocator branch is a premise.
Even malformed choices retain old bases; their errors remain errors. External
addresses here are raw source hook data, not effects of an arbitrary callback. -/
theorem assignment_retains (addresses : GlobalAddressState) (id : AllocId)
    (info : Option AllocationAddressInfo) (choices : AddressRandomChoices)
    (hooks : AddressExternalHooks) :
    Retains addresses (addresses.addrFromAllocId id info choices hooks).state := by
  intro query known found
  unfold GlobalAddressState.addrFromAllocId
  unfold_internal ".GlobalAddressState.findBase"
  unfold_internal ".GlobalAddressState.setGeneration"
  dsimp only [Id.run, bind, pure]
  repeat' first
    | exact found
    | (apply returned_retains addresses _ _ id _ query known found
       exact fun _ _ found => found)
    | split

/-- Cross-thread completion preserves every old base for both acquisition
outcomes. An acquisition error stays an error; successful acquisition performs
the actual registration already proved to retain exact lookups. -/
theorem completion_retains (pending : AddressStateResult AddressAssignment)
    (clock : Except String Unit) :
    Retains pending.state (GlobalAddressState.completeAcquire pending clock).state := by
  unfold GlobalAddressState.completeAcquire
  cases pending.outcome with
  | error error => exact fun _ _ found => found
  | ok assignment =>
    cases assignment with
    | ready base => exact fun _ _ found => found
    | acquireRequired id base vc =>
      cases clock with
      | error message => exact fun _ _ found => found
      | ok acquired =>
        cases acquired
        exact returned_retains pending.state pending.state (fun _ _ found => found) id base

/-- Exposure changes exposure/TB metadata, never a base lookup. No successful
exposure or tracking hook is assumed; partial-error states retain the cache. -/
theorem exposure_retains (addresses : GlobalAddressState) (provenance : Provenance)
    (live : Option Bool) (tracking : Bool) (hook : Option (Except String Unit)) :
    Retains addresses (addresses.exposeProvenance provenance live tracking hook).state := by
  cases provenance with
  | wildcard => exact fun _ _ found => found
  | concrete id tag =>
    unfold GlobalAddressState.exposeProvenance
    dsimp only
    split
    · exact fun _ _ found => found
    · cases live with
      | none => exact fun _ _ found => found
      | some live =>
        cases live with
        | false => exact fun _ _ found => found
        | true =>
          cases tracking with
          | false => exact fun _ _ found => found
          | true =>
            cases hook with
            | none => exact fun _ _ found => found
            | some outcome => cases outcome <;> exact fun _ _ found => found

/-- Raw all-live cache WF is preserved uniformly by assignment followed by
cross-thread completion, for arbitrary source choices and clock outcomes.
The same memory supplies liveness throughout this address-only operation. -/
theorem assignment_live_cached {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (addresses : GlobalAddressState) (wf : LiveCached memory addresses)
    (id : AllocId) (info : Option AllocationAddressInfo) (choices : AddressRandomChoices)
    (hooks : AddressExternalHooks) (clock : Except String Unit) :
    LiveCached memory (GlobalAddressState.completeAcquire
      (addresses.addrFromAllocId id info choices hooks) clock).state :=
  (completion_retains _ clock).live_cached
    ((assignment_retains addresses id info choices hooks).live_cached wf)

/-- A concrete pointer into any initially cached live allocation normalizes
through the unchanged actual resolver after arbitrary assignment/reuse choices.
The old base is raw WF data, not assumed successful pointer resolution. -/
theorem resolver_after_assignment (addresses : GlobalAddressState)
    (assigned : AllocId) (info : Option AllocationAddressInfo) (choices : AddressRandomChoices)
    (hooks : AddressExternalHooks) (clock : Except String Unit)
    (id : AllocId) (base offset : UInt64) (tag : BorTag) (accessSize : Int64)
    (lookup : AddressLookupHooks)
    (cached : addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩) :
    (GlobalAddressState.completeAcquire
      (addresses.addrFromAllocId assigned info choices hooks) clock).state.ptrGetAlloc
        (Pointer.new (.concrete id tag) (Size.ofBytes (base + offset))) accessSize lookup
        ⟨Size.ofBytes 8⟩ = .ok (some (id, Size.ofBytes offset)) := by
  have retained := completion_retains (addresses.addrFromAllocId assigned info choices hooks) clock
    id base (assignment_retains addresses assigned info choices hooks id base cached)
  exact MemoryCopyBridge.ptr_get_alloc_cached _ id tag base offset accessSize lookup _ rfl retained

end DuplicatePrefix.OrdinaryAddressCachePreservation
