import duplicate_prefix.MemoryCopyBridge
import duplicate_prefix.PointerAccess
import Miri.Interpreter.TypedValidityProviders

/-! Canonical pointer leaves used by the stateful typed retag driver. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.RetagPointerChecks
open Miri.ABI Miri.Memory Miri.Memory.AllocAddresses Miri.Interpreter
open Lean Elab

elab "retag_validity_resolve" : term => do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith ".ValidityMachine.resolve" then some name else none
  match names with
  | [name] => return mkConst name
  | _ => throwError "expected exact validity resolver"

private theorem validity_resolve_of_exact {K U : Type}
    (access : ValidityMachine.Access K U) (state : ValidityMachine.State K U)
    (pointer : Pointer (Option Provenance)) (size : Int)
    (resolved : ResolvedPointer ProvenanceExtra)
    (exactResolution : access.resolvePointer state.machine.memory pointer size state.machine =
      .ok (.ok resolved) state.machine) :
    retag_validity_resolve access pointer size state = .ok (.ok resolved) state := by
  unfold_internal ".ValidityMachine.resolve"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, set, EStateM.set, exactResolution]

theorem resolve_allocation_cached {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (state : ValidityMachine.State K U)
    (id : AllocId) (tag : BorTag) (base offset : UInt64)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩) :
    TypedValidityProviders.resolveAllocation pointers
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) state =
      .ok (some ⟨id, Size.ofBytes offset, .concrete tag⟩) state := by
  have resolved := MemoryCopyBridge.ptr_get_alloc_cached state.machine.user.addresses
    id tag base offset (Int64.ofInt 0)
    { sizeOf := fun id => (state.machine.memory.getAllocInfo id).toOption.map (·.size)
      isLive := fun id => some (state.machine.memory.isAllocLive id) }
    pointers.arithmetic width cached
  unfold TypedValidityProviders.resolveAllocation PointerMachine.resolvePointer
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, Pointer.new]
  simp only [Pointer.new] at resolved
  simp only [Id.run, bind, pure, EStateM.bind, EStateM.pure, set, EStateM.set]
  erw [resolved]
  rfl

#print axioms resolve_allocation_cached

private theorem pure_check_stage
    (target : PointerArithmetic) (pointer : Pointer (Option Provenance))
    (size : Size) (signed : Int)
    (resolve : PointerResolver Provenance ProvenanceExtra) (lookup : LiveAllocationLookup)
    (resolved : ResolvedPointer ProvenanceExtra) (info : AllocationInfo)
    (sizeEq : sizeAsI64 size = .ok signed)
    (dereferenced : checkAndDerefPtr target pointer signed (.dereferenceable "pointer")
      resolve lookup = .ok (some ⟨resolved, info⟩)) :
    checkPtrAccess target pointer size (.dereferenceable "pointer") resolve lookup = .ok () := by
  unfold checkPtrAccess
  rw [sizeEq]
  simp only [bind, Except.bind]
  rw [dereferenced]
  rfl

private theorem pure_pointer_access {K : Type}
    (target : PointerArithmetic) (memory : MemoryState Provenance Miri.TreeBorrows.BorrowTree K)
    (id : AllocId) (tag : BorTag) (base offset len : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (present : memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (positive : 0 < len.toNat) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    checkPtrAccess target
      (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base + offset)))
      (Size.ofBytes len) (.dereferenceable "pointer")
      (fun _ _ => .ok ⟨id, Size.ofBytes offset, ProvenanceExtra.concrete tag⟩)
      memory.getAllocInfo = .ok () := by
  have signed := DuplicatePrefix.signed_size_ok (Size.ofBytes len) signedFits
  change sizeAsI64 (Size.ofBytes len) = .ok (Int.ofNat len.toNat) at signed
  have info := MemoryCopyBridge.live_alloc_info memory id entry present
  have dereferenced := PointerAccess.dereference_ok target
    (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base + offset))) len.toNat
    (.dereferenceable "pointer") (fun _ _ => .ok ⟨id, Size.ofBytes offset, ProvenanceExtra.concrete tag⟩)
    memory.getAllocInfo ⟨id, Size.ofBytes offset, ProvenanceExtra.concrete tag⟩
    ⟨entry.allocation.byteSize, entry.allocation.align, .liveData, entry.allocation.mutability⟩
    positive signedFits rfl info (by simp) bounds
  exact pure_check_stage target _ _ _ _ _ _ _ signed dereferenced

private theorem check_pointer_stage {K U : Type}
    (access : ValidityMachine.Access K U) (state : ValidityMachine.State K U)
    (pointer : Pointer (Option Provenance)) (size : Size) (signed : Int)
    (resolved : ResolvedPointer ProvenanceExtra)
    (sizeEq : sizeAsI64 size = .ok signed)
    (nonzero : (signed == 0) = false)
    (resolution : retag_validity_resolve access pointer signed state = .ok (.ok resolved) state)
    (checked : checkPtrAccess ⟨access.runtime.pointerSize⟩ pointer size
      (.dereferenceable "pointer") (fun _ _ => .ok resolved)
      state.machine.memory.getAllocInfo = .ok ()) :
    ValidityMachine.checkPointerAccess access pointer size state = .ok () state := by
  unfold ValidityMachine.checkPointerAccess ValidityMachine.checkPointerAccessResult
  simp only [sizeEq, bind, EStateM.bind, pure, EStateM.pure,
    nonzero, Bool.false_eq_true, ↓reduceIte, resolution, get, getThe,
    MonadStateOf.get, EStateM.get]
  erw [checked]
  rfl

theorem check_pointer_access_cached {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (access : ValidityMachine.Access K U) (state : ValidityMachine.State K U)
    (id : AllocId) (tag : BorTag) (base offset len : UInt64)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (wiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (positive : (0 : UInt64) < len)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat) :
    ValidityMachine.checkPointerAccess access
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset)))
      (Size.ofBytes len) state = .ok () state := by
  have signed := DuplicatePrefix.signed_size_ok (Size.ofBytes len) signedFits
  change sizeAsI64 (Size.ofBytes len) = .ok (Int.ofNat len.toNat) at signed
  have positiveNat : 0 < len.toNat := by
    simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using positive
  have resolved := MemoryCopyBridge.typed_resolve_cached pointers state.machine.memory state.machine
    id tag base offset (Int.ofNat len.toNat) width
    (by change -(2 ^ 63 : Int) ≤ (len.toNat : Int); omega)
    (by change (len.toNat : Int) < (2 ^ 63 : Int); omega) cached
  have resolveStep := validity_resolve_of_exact access state
    (Pointer.new (some (Provenance.concrete id tag)) (Size.ofBytes (base + offset)))
    (Int.ofNat len.toNat) ⟨id, Size.ofBytes offset, .concrete tag⟩
    (by rw [wiring]; exact resolved)
  have checked := pure_pointer_access ⟨access.runtime.pointerSize⟩ state.machine.memory
    id tag base offset len entry present positiveNat signedFits bounds
  have signedNonzero : (Int.ofNat len.toNat == 0) = false := by simp; omega
  exact check_pointer_stage access state _ _ _ _ signed signedNonzero resolveStep checked

#print axioms check_pointer_access_cached

theorem ensure_tree_live {K U : Type} [DecidableEq K]
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance Miri.TreeBorrows.BorrowTree K
      (PlaceMachine.AccessState K U))
    (wiring : globals.synchronizeMemory = fun memory view =>
      {view with machine := {view.machine with memory}})
    (state : MachineHooks.State K U) (id : AllocId)
    (entry : LocalAllocation Provenance Miri.TreeBorrows.BorrowTree K)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry)) :
    GlobalAllocationMachine.ensure globalKind globals id state = .ok () state := by
  have raw := MemoryCopyBridge.get_raw_live state.machine.memory
    (⟨state.machine, none⟩ : PlaceMachine.AccessState K U) id entry
    (some globalKind) globals present
  unfold GlobalAllocationMachine.ensure
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, raw, wiring]
  rfl

#print axioms ensure_tree_live

theorem check_pointer_zero {K U : Type} (access : ValidityMachine.Access K U)
    (pointer : Pointer (Option Provenance)) (state : ValidityMachine.State K U) :
    ValidityMachine.checkPointerAccess access pointer Size.ZERO state = .ok () state := by
  unfold ValidityMachine.checkPointerAccess ValidityMachine.checkPointerAccessResult
  simp [sizeAsI64, Size.ZERO, bind, EStateM.bind, pure, EStateM.pure]

theorem resolve_allocation_none {K U : Type}
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (pointer : Pointer (Option Provenance)) (state : ValidityMachine.State K U)
    (noProvenance : pointer.provenance = none) :
    TypedValidityProviders.resolveAllocation pointers pointer state = .ok none state := by
  unfold TypedValidityProviders.resolveAllocation PointerMachine.resolvePointer
  simp [noProvenance, Id.run, bind, EStateM.bind, pure, EStateM.pure,
    get, getThe, MonadStateOf.get, EStateM.get, set, EStateM.set]

#print axioms check_pointer_zero
#print axioms resolve_allocation_none
end DuplicatePrefix.RetagPointerChecks

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.RetagPointerChecks.resolve_allocation_cached,
      ``DuplicatePrefix.RetagPointerChecks.check_pointer_access_cached,
      ``DuplicatePrefix.RetagPointerChecks.ensure_tree_live,
      ``DuplicatePrefix.RetagPointerChecks.check_pointer_zero,
      ``DuplicatePrefix.RetagPointerChecks.resolve_allocation_none] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
