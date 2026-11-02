import duplicate_prefix.MemoryCopyBridge
import duplicate_prefix.OrdinaryPhysicalValidity

namespace DuplicatePrefix.OrdinaryPointerCacheBoundary
open Miri Miri.ABI Miri.Memory Miri.Memory.AllocAddresses
open Miri.Interpreter Miri.TreeBorrows
set_option autoImplicit false

/-- Exact concrete resolution from raw cache contents. Concrete resolution
uses neither heap liveness nor borrow permissions; those checks occur later.
This is normalization evidence, not evidence of reference ownership. -/
theorem concrete_resolution (addresses : GlobalAddressState) (id : AllocId)
    (tag : BorTag) (address : UInt64) (row : BaseAddressEntry)
    (accessSize : Int64) (lookup : AddressLookupHooks)
    (cached : addresses.baseAddr.find? (fun entry => entry.allocId == id) = some row) :
    addresses.ptrGetAlloc (Pointer.new (.concrete id tag) (Size.ofBytes address))
      accessSize lookup ⟨Size.ofBytes 8⟩ =
      .ok (some (id, Size.ofBytes (address - row.address))) := by
  unfold GlobalAddressState.ptrGetAlloc
  unfold_internal ".GlobalAddressState.findBase"
  simp only [Pointer.new, cached, Option.map_some, Bind.bind, Except.bind,
    Pure.pure, Except.pure, Size.ofBytes]
  erw [DuplicatePrefix.PointerArithmetic.truncate_u64_identity]
  rfl

/-- The cache requirement is a real fixed-resolver boundary, not a condition
that can be erased using only physical slice validity. An absent concrete base
produces this exact error, even when later allocation/value checks would pass.
The theorem assumes no successful operation and makes no reachable-history or
ordinary-valid-caller counterexample claim. -/
theorem concrete_missing_base (addresses : GlobalAddressState) (id : AllocId)
    (tag : BorTag) (address : UInt64) (accessSize : Int64)
    (lookup : AddressLookupHooks) (arithmetic : PointerArithmetic)
    (absent : addresses.baseAddr.find? (fun entry => entry.allocId == id) = none) :
    addresses.ptrGetAlloc (Pointer.new (.concrete id tag) (Size.ofBytes address))
      accessSize lookup arithmetic = .error (.missingBaseAddress id) := by
  unfold GlobalAddressState.ptrGetAlloc
  unfold_internal ".GlobalAddressState.findBase"
  simp only [Pointer.new, absent, Option.map_none, Bind.bind, Except.bind,
    Pure.pure, Except.pure]
  rfl

/-- The same missing-base boundary reaches the actual typed resolver unchanged,
with its actual error classifier and unchanged machine state. -/
theorem typed_missing_base {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (memory : MemoryState Provenance BorrowTree K)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (address : UInt64) (accessSize : Int)
    (lower : -(2^63 : Int) ≤ accessSize) (upper : accessSize < (2^63 : Int))
    (absent : machine.user.addresses.baseAddr.find? (fun entry => entry.allocId == id) = none) :
    TypedMemoryProviders.resolvePointer pointers memory
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes address)) accessSize machine =
      .error (pointers.classifyAddressError (.missingBaseAddress id)) machine := by
  unfold TypedMemoryProviders.resolvePointer
  have lowerFalse : decide (accessSize < -(2^63 : Int)) = false := by simp; omega
  have upperFalse : decide (accessSize ≥ (2^63 : Int)) = false := by simp; omega
  simp only [Pointer.new, lowerFalse, upperFalse, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte]
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    pure]
  erw [concrete_missing_base machine.user.addresses id tag address
    (Int64.ofInt accessSize) _ pointers.arithmetic absent]
  rfl

/-- For concrete pointers in the fixed 64-bit model, raw cache membership is
EXACTLY the condition for address resolution. This equivalence does not turn
successful address resolution into an assumed input-domain condition. -/
theorem concrete_cache_iff (addresses : GlobalAddressState) (id : AllocId)
    (tag : BorTag) (address : UInt64) (accessSize : Int64) (lookup : AddressLookupHooks) :
    (∃ row, addresses.baseAddr.find? (fun entry => entry.allocId == id) = some row) ↔
    (∃ offset, addresses.ptrGetAlloc (Pointer.new (.concrete id tag) (Size.ofBytes address))
      accessSize lookup ⟨Size.ofBytes 8⟩ = .ok (some (id, offset))) := by
  constructor
  · rintro ⟨row, cached⟩
    exact ⟨_, concrete_resolution addresses id tag address row accessSize lookup cached⟩
  · intro resolved
    cases cached : addresses.baseAddr.find? (fun entry => entry.allocId == id) with
    | some row => exact ⟨row, rfl⟩
    | none =>
      obtain ⟨offset, resolved⟩ := resolved
      rw [concrete_missing_base addresses id tag address accessSize lookup _ cached] at resolved
      cases resolved

/-- The physical slice component does not constrain the global base cache:
for every physically valid slice, the same allocation admits an empty-cache
address packet, whose concrete resolution fails exactly at the missing base.
Therefore a physical-only adapter cannot construct the existing cachedBase
field. A complete ordinary-call bridge must separately justify cache formation
as machine wellformedness; address-cache insertion is not performed by this
fixed resolver. This is not a full valid machine counterexample. -/
theorem physical_slice_without_base {allocation : Allocation Provenance BorrowTree}
    {offset len : UInt64} (physical : OrdinaryPhysicalValidity.MutU8Slice allocation offset len)
    (addresses : GlobalAddressState) (id : AllocId) (tag : BorTag) (address : UInt64)
    (accessSize : Int64) (lookup : AddressLookupHooks) (arithmetic : PointerArithmetic) :
    OrdinaryPhysicalValidity.MutU8Slice allocation offset len ∧
      ({addresses with baseAddr := #[]} : GlobalAddressState).ptrGetAlloc
        (Pointer.new (.concrete id tag) (Size.ofBytes address)) accessSize lookup arithmetic =
        .error (.missingBaseAddress id) := by
  refine ⟨physical, concrete_missing_base _ id tag address accessSize lookup arithmetic ?_⟩
  simp

end DuplicatePrefix.OrdinaryPointerCacheBoundary
