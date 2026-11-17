import duplicate_prefix.PhysicalScalarReturn
import duplicate_prefix.RetagPointerChecks
import duplicate_prefix.RetagEntry
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.S04ReturnWindowPointer
open Miri.ABI Miri.Memory Miri.Interpreter Miri.TreeBorrows

private def accessPrefix {Prov Extra K S PX : Type} [DecidableEq K]
    (initialMemory : MemoryState Prov Extra K) (initialHooks : S)
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Size)
    (ghostMode : Bool) (globalKind : Option K)
    (globalHooks : GlobalAllocationHooks Prov Extra K S)
    (accessHooks : AllocationAccessHooks Prov Extra K S PX) (write : Bool)
    (finishNext : MemoryState Prov Extra K → S →
      Option (ResolvedPointer PX × AllocationAccessRef Prov Extra) → Int →
      PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra))) :
    PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra)) := Id.run do
  let mut memory := initialMemory
  let mut hookState := initialHooks
  let signedSize ← match sizeAsI64 size with
    | .ok amount => pure amount
    | .error error => return ⟨memory, hookState, none, .error (.access error)⟩
  let mut checked : Option (ResolvedPointer PX × AllocationAccessRef Prov Extra) := none
  if signedSize != 0 then
    let resolution := accessHooks.resolvePointer memory hookState ptr signedSize
    hookState := resolution.state
    let resolved ← match resolution.outcome with
      | .error message => return ⟨memory, hookState, none,
          .error (.hookFailure "ptrTryGetAllocId" message)⟩
      | .ok (.error address) => return ⟨memory, hookState, none,
          .error (.access (.danglingIntegerPointer address signedSize .memoryAccess))⟩
      | .ok (.ok resolved) => pure resolved
    let raw := if write then
        MemoryLifecycle.getAllocRawMut memory hookState resolved.allocId globalKind globalHooks
      else MemoryLifecycle.getAllocRaw memory hookState resolved.allocId globalKind globalHooks
    memory := raw.memory
    hookState := raw.hooks
    let allocation ← match raw.outcome with
      | .ok allocation => pure allocation
      | .error error => return ⟨memory, hookState, none, .error (.rawAccess error)⟩
    let reference : AllocationAccessRef Prov Extra :=
      ⟨resolved.allocId, allocRange resolved.offset size, allocation⟩
    match checkedBounds target resolved.allocId allocation.byteSize resolved.offset signedSize .memoryAccess with
    | .error error => return ⟨memory, hookState, some reference, .error (.access error)⟩
    | .ok () => checked := some (resolved, reference)
  return finishNext memory hookState checked signedSize

private def accessFinish {Prov Extra K S PX : Type} [DecidableEq K]
    (initialMemory : MemoryState Prov Extra K) (initialHooks : S)
    (ptr : Pointer (Option Prov)) (signedSize : Int) (ghostMode : Bool)
    (accessHooks : AllocationAccessHooks Prov Extra K S PX) (write : Bool)
    (initialChecked : Option (ResolvedPointer PX × AllocationAccessRef Prov Extra)) :
    PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra)) := Id.run do
  let mut memory := initialMemory
  let mut hookState := initialHooks
  let mut checked := initialChecked
  if !ghostMode then
    let accessId ← if write then
        pure (checked.map fun (_, reference) => reference.allocId)
      else do
        -- The source deliberately resolves again, including size-zero reads.
        let resolution := accessHooks.resolvePointer memory hookState ptr signedSize
        hookState := resolution.state
        match resolution.outcome with
        | .error message => return ⟨memory, hookState, checked.map Prod.snd,
            .error (.hookFailure "ptrTryGetAllocId" message)⟩
        | .ok (.error _) => pure none
        | .ok (.ok resolved) => pure (some resolved.allocId)
    if let some accessId := accessId then
      let access := accessHooks.beforeAllocationAccess hookState accessId
      hookState := access.state
      if let .error message := access.outcome then
        return ⟨memory, hookState, checked.map Prod.snd,
          .error (.hookFailure "beforeAllocAccess" message)⟩
    if let some (resolved, reference) := checked then
      let access := if write then
          accessHooks.beforeMemoryWrite hookState reference.allocation.extra ptr
            reference.allocId resolved.extra reference.range
        else accessHooks.beforeMemoryRead hookState reference.allocation.extra ptr
            reference.allocId resolved.extra reference.range
      hookState := access.state
      let updated := { reference with allocation := reference.allocation.setExtra access.extra }
      -- Borrowed CTFE globals have no local cache entry. Miri's owned global
      -- conversions and all mutable accesses do have one.
      if memory.live.any (fun entry => entry.1 == reference.allocId) then
        match memory.setLiveAllocation reference.allocId updated.allocation with
        | .ok afterUpdate => memory := afterUpdate
        | .error error => return ⟨memory, hookState, some updated, .error (.cacheUpdate error)⟩
      checked := some (resolved, updated)
      if let .error message := access.outcome then
        return ⟨memory, hookState, some updated,
          .error (.hookFailure (if write then "beforeMemoryWrite" else "beforeMemoryRead") message)⟩
  let reference := checked.map Prod.snd
  return ⟨memory, hookState, reference, .ok reference⟩


private theorem access_program {Prov Extra K S PX : Type} [DecidableEq K]
    (memory : MemoryState Prov Extra K) (hooks : S)
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Size)
    (ghostMode : Bool) (globalKind : Option K)
    (globalHooks : GlobalAllocationHooks Prov Extra K S)
    (accessHooks : AllocationAccessHooks Prov Extra K S PX) :
    AllocationAccess.getPtrAllocMut memory hooks target ptr size ghostMode globalKind globalHooks accessHooks =
      accessPrefix memory hooks target ptr size ghostMode globalKind globalHooks accessHooks true
        (fun memory hooks checked signed => accessFinish memory hooks ptr signed ghostMode accessHooks true checked) := by
  unfold AllocationAccess.getPtrAllocMut
  unfold_internal ".AllocationAccess.getPtrAllocation"
  unfold accessPrefix accessFinish
  rfl
#print axioms access_program

private def accessRaw {Prov Extra K S PX : Type} [DecidableEq K]
    (memory : MemoryState Prov Extra K) (hooks : S) (target : PointerArithmetic)
    (resolved : ResolvedPointer PX) (size : Size) (signedSize : Int)
    (globalKind : Option K) (globalHooks : GlobalAllocationHooks Prov Extra K S) (write : Bool)
    (finishNext : MemoryState Prov Extra K → S → Option (ResolvedPointer PX × AllocationAccessRef Prov Extra) → Int →
      PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra))) :
    PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra)) := Id.run do
  let raw := if write then MemoryLifecycle.getAllocRawMut memory hooks resolved.allocId globalKind globalHooks
    else MemoryLifecycle.getAllocRaw memory hooks resolved.allocId globalKind globalHooks
  let allocation ← match raw.outcome with
    | .ok allocation => pure allocation
    | .error error => return ⟨raw.memory,raw.hooks,none,.error (.rawAccess error)⟩
  let reference : AllocationAccessRef Prov Extra := ⟨resolved.allocId,allocRange resolved.offset size,allocation⟩
  match checkedBounds target resolved.allocId allocation.byteSize resolved.offset signedSize .memoryAccess with
  | .error error => return ⟨raw.memory,raw.hooks,some reference,.error (.access error)⟩
  | .ok () => return finishNext raw.memory raw.hooks (some (resolved,reference)) signedSize

private def accessResolve {Prov Extra K S PX : Type} [DecidableEq K]
    (memory : MemoryState Prov Extra K) (hooks : S) (ptr : Pointer (Option Prov)) (size : Size)
    (accessHooks : AllocationAccessHooks Prov Extra K S PX)
    (resolvedNext : MemoryState Prov Extra K → S → ResolvedPointer PX → Int →
      PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra)))
    (finishNext : MemoryState Prov Extra K → S → Option (ResolvedPointer PX × AllocationAccessRef Prov Extra) → Int →
      PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra))) :
    PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra)) := Id.run do
  let signed ← match sizeAsI64 size with
    | .ok signed => pure signed
    | .error error => return ⟨memory,hooks,none,.error (.access error)⟩
  if signed != 0 then
    let resolution := accessHooks.resolvePointer memory hooks ptr signed
    let resolved ← match resolution.outcome with
      | .error message => return ⟨memory,resolution.state,none,.error (.hookFailure "ptrTryGetAllocId" message)⟩
      | .ok (.error address) => return ⟨memory,resolution.state,none,
          .error (.access (.danglingIntegerPointer address signed .memoryAccess))⟩
      | .ok (.ok resolved) => pure resolved
    return resolvedNext memory resolution.state resolved signed
  return finishNext memory hooks none signed

private theorem prefix_program {Prov Extra K S PX : Type} [DecidableEq K]
    (memory : MemoryState Prov Extra K) (hooks : S)
    (target : PointerArithmetic) (ptr : Pointer (Option Prov)) (size : Size)
    (ghostMode : Bool) (globalKind : Option K)
    (globalHooks : GlobalAllocationHooks Prov Extra K S)
    (accessHooks : AllocationAccessHooks Prov Extra K S PX) (write : Bool)
    (finishNext : MemoryState Prov Extra K → S → Option (ResolvedPointer PX × AllocationAccessRef Prov Extra) → Int →
      PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra))) :
    accessPrefix memory hooks target ptr size ghostMode globalKind globalHooks accessHooks write finishNext =
      accessResolve memory hooks ptr size accessHooks
        (fun memory hooks resolved signed => accessRaw memory hooks target resolved size signed globalKind globalHooks write finishNext)
        finishNext := by
  unfold accessPrefix accessResolve accessRaw
  rfl
#print axioms prefix_program

private theorem access_finish_write {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset count capacity : UInt64)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes capacity)
    (bounds : offset.toNat + count.toNat ≤ capacity.toNat)
    (mutable : entry.allocation.mutability = .Mut)
    (synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (before : config.beforeAllocationAccess = fun _ => pure ())
    (access : PlaceMachine.memoryAccess config true ⟨machine,none⟩ entry.allocation.extra id (.concrete tag)
      (allocRange (Size.ofBytes offset) (Size.ofBytes count)) = ⟨⟨machine,none⟩,tree,.ok ()⟩)
    (signedLeaf : sizeAsI64 (Size.ofBytes count) = .ok (Int.ofNat count.toNat))
    (nonzeroLeaf : (Int.ofNat count.toNat != 0) = true)
    (resolveLeaf : config.resolvePointer machine.memory
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Int.ofNat count.toNat) machine =
      .ok (.ok ⟨id,(Size.ofBytes offset),.concrete tag⟩) machine)
    (rawLeaf : MemoryLifecycle.getAllocRawMut machine.memory (PlaceMachine.AccessState.mk machine none)
      id config.globalKind config.globalHooks = ⟨machine.memory,⟨machine,none⟩,.ok entry.allocation⟩)
    (checkedLeaf : checkedBounds ⟨Size.ofBytes 8⟩ id entry.allocation.byteSize (Size.ofBytes offset)
      (Int.ofNat count.toNat) .memoryAccess = .ok ())
    (storedLeaf : machine.memory.setLiveAllocation id (entry.allocation.setExtra tree) =
      .ok (RetagEntry.updatedMemory machine.memory id entry tree))
    (containsLeaf : machine.memory.live.any (fun row => row.1 == id) = true) :
    accessFinish machine.memory ⟨machine,none⟩
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Int.ofNat count.toNat) false
      (PlaceMachine.accessHooks config) true
      (some (⟨id,(Size.ofBytes offset),.concrete tag⟩,⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation⟩)) =
      ⟨RetagEntry.updatedMemory machine.memory id entry tree, ⟨machine,none⟩,
        some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation.setExtra tree⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation.setExtra tree⟩)⟩ := by
  unfold accessFinish
  simp only [Bool.not_false, Bool.true_eq, ↓reduceIte, Option.map_some, Bind.bind, Pure.pure, Id.instMonad,
    PlaceMachine.accessHooks]
  unfold_internal ".PlaceMachine.bridge"
  simp only [before, pure, EStateM.pure]
  erw [access]
  simp only [containsLeaf, Bool.true_eq, ↓reduceIte]
  erw [storedLeaf]
  simp only [Option.map_some]
  rfl
#print axioms access_finish_write

private theorem resolve_write {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset count capacity : UInt64)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes capacity)
    (bounds : offset.toNat + count.toNat ≤ capacity.toNat)
    (mutable : entry.allocation.mutability = .Mut)
    (synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (before : config.beforeAllocationAccess = fun _ => pure ())
    (access : PlaceMachine.memoryAccess config true ⟨machine,none⟩ entry.allocation.extra id (.concrete tag)
      (allocRange (Size.ofBytes offset) (Size.ofBytes count)) = ⟨⟨machine,none⟩,tree,.ok ()⟩)
    (signedLeaf : sizeAsI64 (Size.ofBytes count) = .ok (Int.ofNat count.toNat))
    (nonzeroLeaf : (Int.ofNat count.toNat != 0) = true)
    (resolveLeaf : config.resolvePointer machine.memory
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Int.ofNat count.toNat) machine =
      .ok (.ok ⟨id,(Size.ofBytes offset),.concrete tag⟩) machine)
    (rawLeaf : MemoryLifecycle.getAllocRawMut machine.memory (PlaceMachine.AccessState.mk machine none)
      id config.globalKind config.globalHooks = ⟨machine.memory,⟨machine,none⟩,.ok entry.allocation⟩)
    (checkedLeaf : checkedBounds ⟨Size.ofBytes 8⟩ id entry.allocation.byteSize (Size.ofBytes offset)
      (Int.ofNat count.toNat) .memoryAccess = .ok ())
    (storedLeaf : machine.memory.setLiveAllocation id (entry.allocation.setExtra tree) =
      .ok (RetagEntry.updatedMemory machine.memory id entry tree))
    (containsLeaf : machine.memory.live.any (fun row => row.1 == id) = true)
    (finishNext : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K (ValidityMachine.UserState U) →
      Option (ResolvedPointer ProvenanceExtra × AllocationAccessRef Provenance BorrowTree) → Int →
      PtrAllocationResult Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U))
        (Option (AllocationAccessRef Provenance BorrowTree)))
    (resolvedNext : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K (ValidityMachine.UserState U) →
      ResolvedPointer ProvenanceExtra → Int →
      PtrAllocationResult Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U))
        (Option (AllocationAccessRef Provenance BorrowTree))) :
    accessResolve machine.memory ⟨machine,none⟩
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Size.ofBytes count)
      (PlaceMachine.accessHooks config) resolvedNext finishNext =
      resolvedNext machine.memory ⟨machine,none⟩ ⟨id,(Size.ofBytes offset),.concrete tag⟩ (Int.ofNat count.toNat) := by
  unfold accessResolve
  simp only [signedLeaf, Bind.bind, Pure.pure, Id.instMonad, nonzeroLeaf, Bool.true_eq, ↓reduceIte, PlaceMachine.accessHooks]
  unfold_internal ".PlaceMachine.bridge"
  erw [resolveLeaf]
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  rfl
#print axioms resolve_write

private def accessRawResult {Prov Extra K S PX : Type}
    (raw : MemoryAccessResult Prov Extra K S (Allocation Prov Extra))
    (target : PointerArithmetic) (resolved : ResolvedPointer PX) (size : Size) (signedSize : Int)
    (finishNext : MemoryState Prov Extra K → S → Option (ResolvedPointer PX × AllocationAccessRef Prov Extra) → Int →
      PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra))) :
    PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra)) := Id.run do
  let allocation ← match raw.outcome with
    | .ok allocation => pure allocation
    | .error error => return ⟨raw.memory,raw.hooks,none,.error (.rawAccess error)⟩
  let reference : AllocationAccessRef Prov Extra := ⟨resolved.allocId,allocRange resolved.offset size,allocation⟩
  match checkedBounds target resolved.allocId allocation.byteSize resolved.offset signedSize .memoryAccess with
  | .error error => return ⟨raw.memory,raw.hooks,some reference,.error (.access error)⟩
  | .ok () => return finishNext raw.memory raw.hooks (some (resolved,reference)) signedSize

private theorem raw_program {Prov Extra K S PX : Type} [DecidableEq K]
    (memory : MemoryState Prov Extra K) (hooks : S) (target : PointerArithmetic)
    (resolved : ResolvedPointer PX) (size : Size) (signedSize : Int)
    (globalKind : Option K) (globalHooks : GlobalAllocationHooks Prov Extra K S) (write : Bool)
    (finishNext : MemoryState Prov Extra K → S → Option (ResolvedPointer PX × AllocationAccessRef Prov Extra) → Int →
      PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra))) :
    accessRaw memory hooks target resolved size signedSize globalKind globalHooks write finishNext =
      accessRawResult (if write then MemoryLifecycle.getAllocRawMut memory hooks resolved.allocId globalKind globalHooks
        else MemoryLifecycle.getAllocRaw memory hooks resolved.allocId globalKind globalHooks)
        target resolved size signedSize finishNext := by rfl

private theorem raw_result_ok {Prov Extra K S PX : Type}
    (raw : MemoryAccessResult Prov Extra K S (Allocation Prov Extra))
    (memory : MemoryState Prov Extra K) (hooks : S) (allocation : Allocation Prov Extra)
    (target : PointerArithmetic) (resolved : ResolvedPointer PX) (size : Size) (signed : Int)
    (rawEq : raw = ⟨memory,hooks,.ok allocation⟩)
    (checked : checkedBounds target resolved.allocId allocation.byteSize resolved.offset signed .memoryAccess = .ok ())
    (finishNext : MemoryState Prov Extra K → S → Option (ResolvedPointer PX × AllocationAccessRef Prov Extra) → Int →
      PtrAllocationResult Prov Extra K S (Option (AllocationAccessRef Prov Extra))) :
    accessRawResult raw target resolved size signed finishNext =
      finishNext memory hooks (some (resolved,⟨resolved.allocId,allocRange resolved.offset size,allocation⟩)) signed := by
  rw [rawEq]
  unfold accessRawResult
  simp only [Bind.bind, Pure.pure, Id.instMonad]
  rw [checked]
  rfl
#print axioms raw_result_ok

private theorem raw_write {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset count capacity : UInt64)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes capacity)
    (bounds : offset.toNat + count.toNat ≤ capacity.toNat)
    (mutable : entry.allocation.mutability = .Mut)
    (synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (before : config.beforeAllocationAccess = fun _ => pure ())
    (access : PlaceMachine.memoryAccess config true ⟨machine,none⟩ entry.allocation.extra id (.concrete tag)
      (allocRange (Size.ofBytes offset) (Size.ofBytes count)) = ⟨⟨machine,none⟩,tree,.ok ()⟩)
    (signedLeaf : sizeAsI64 (Size.ofBytes count) = .ok (Int.ofNat count.toNat))
    (nonzeroLeaf : (Int.ofNat count.toNat != 0) = true)
    (resolveLeaf : config.resolvePointer machine.memory
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Int.ofNat count.toNat) machine =
      .ok (.ok ⟨id,(Size.ofBytes offset),.concrete tag⟩) machine)
    (rawLeaf : MemoryLifecycle.getAllocRawMut machine.memory (PlaceMachine.AccessState.mk machine none)
      id config.globalKind config.globalHooks = ⟨machine.memory,⟨machine,none⟩,.ok entry.allocation⟩)
    (checkedLeaf : checkedBounds ⟨Size.ofBytes 8⟩ id entry.allocation.byteSize (Size.ofBytes offset)
      (Int.ofNat count.toNat) .memoryAccess = .ok ())
    (storedLeaf : machine.memory.setLiveAllocation id (entry.allocation.setExtra tree) =
      .ok (RetagEntry.updatedMemory machine.memory id entry tree))
    (containsLeaf : machine.memory.live.any (fun row => row.1 == id) = true)
    (finishNext : MemoryState Provenance BorrowTree K → PlaceMachine.AccessState K (ValidityMachine.UserState U) →
      Option (ResolvedPointer ProvenanceExtra × AllocationAccessRef Provenance BorrowTree) → Int →
      PtrAllocationResult Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U))
        (Option (AllocationAccessRef Provenance BorrowTree))) :
    accessRaw machine.memory ⟨machine,none⟩ ⟨Size.ofBytes 8⟩ ⟨id,(Size.ofBytes offset),.concrete tag⟩
      (Size.ofBytes count) (Int.ofNat count.toNat) config.globalKind config.globalHooks true finishNext =
      finishNext machine.memory ⟨machine,none⟩
        (some (⟨id,(Size.ofBytes offset),.concrete tag⟩,⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation⟩))
        (Int.ofNat count.toNat) := by
  rw [raw_program]
  simp only [Bool.true_eq, ↓reduceIte]
  exact @raw_result_ok Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)) ProvenanceExtra
    (MemoryLifecycle.getAllocRawMut machine.memory (PlaceMachine.AccessState.mk machine none) id config.globalKind config.globalHooks)
    machine.memory (PlaceMachine.AccessState.mk machine none) entry.allocation
    ⟨Size.ofBytes 8⟩ ⟨id,(Size.ofBytes offset),.concrete tag⟩ (Size.ofBytes count) (Int.ofNat count.toNat)
    rawLeaf checkedLeaf finishNext

#print axioms raw_write

theorem get_ptr_write_of_access {K U : Type} [DecidableEq K]
    (config : PlaceMachine.AccessConfig K (ValidityMachine.UserState U))
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (canonical : config.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (id : AllocId) (tag : BorTag) (base offset count capacity : UInt64)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (positive : (0 : UInt64) < count) (signedFits : count.toNat < 9223372036854775808)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (size : entry.allocation.byteSize = Size.ofBytes capacity)
    (bounds : offset.toNat + count.toNat ≤ capacity.toNat)
    (mutable : entry.allocation.mutability = .Mut)
    (synchronize : config.globalHooks.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (before : config.beforeAllocationAccess = fun _ => pure ())
    (access : PlaceMachine.memoryAccess config true ⟨machine,none⟩ entry.allocation.extra id (.concrete tag)
      (allocRange (Size.ofBytes offset) (Size.ofBytes count)) = ⟨⟨machine,none⟩,tree,.ok ()⟩) :
    AllocationAccess.getPtrAllocMut machine.memory ⟨machine,none⟩ ⟨Size.ofBytes 8⟩
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Size.ofBytes count) false
      config.globalKind config.globalHooks (PlaceMachine.accessHooks config) =
      ⟨RetagEntry.updatedMemory machine.memory id entry tree, ⟨machine,none⟩,
        some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation.setExtra tree⟩,
        .ok (some ⟨id,allocRange (Size.ofBytes offset) (Size.ofBytes count),entry.allocation.setExtra tree⟩)⟩ := by
  have signed := DuplicatePrefix.signed_size_ok (Size.ofBytes count) signedFits
  change sizeAsI64 (Size.ofBytes count) = .ok (Int.ofNat count.toNat) at signed
  have nonzero : (Int.ofNat count.toNat != 0) = true := by
    have positiveNat : 0 < count.toNat := by simpa only [UInt64.lt_iff_toNat_lt, UInt64.toNat_zero] using positive
    simp only [bne_iff_ne]
    change (count.toNat : Int) ≠ 0
    omega
  have resolve := MemoryCopyBridge.typed_resolve_cached pointers machine.memory machine id tag base offset
    (Int.ofNat count.toNat) width
    (by change -(2^63 : Int) ≤ (count.toNat : Int); omega)
    (by change (count.toNat : Int) < (2^63 : Int); omega) cached

  have raw := MemoryCopyBridge.get_raw_mut_live machine.memory (PlaceMachine.AccessState.mk machine none) id entry
    config.globalKind config.globalHooks present mutable
  simp only [synchronize] at raw
  have checked := DuplicatePrefix.checkedBounds_ok ⟨Size.ofBytes 8⟩ id entry.allocation.byteSize (Size.ofBytes offset)
    count.toNat .memoryAccess signedFits (by simpa [size, Size.ofBytes] using bounds)
  have stored := MemoryCopyBridge.set_live_exact machine.memory id entry (entry.allocation.setExtra tree) present
  have contains := MemoryCopyBridge.live_any_of_present machine.memory id entry present
  have resolved : config.resolvePointer machine.memory
      (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Int.ofNat count.toNat) machine =
      .ok (.ok ⟨id,(Size.ofBytes offset),.concrete tag⟩) machine := by
    rw [canonical]
    exact resolve
  rw [access_program, prefix_program]
  let finishNext := fun memory hooks checked signed =>
    accessFinish memory hooks (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) signed false
      (PlaceMachine.accessHooks config) true checked
  let resolvedNext := fun memory hooks resolved signed =>
    accessRaw memory hooks ⟨Size.ofBytes 8⟩ resolved (Size.ofBytes count) signed
      config.globalKind config.globalHooks true finishNext
  change accessResolve machine.memory (PlaceMachine.AccessState.mk machine none)
    (Pointer.new (some (.concrete id tag)) (Size.ofBytes (base + offset))) (Size.ofBytes count)
    (PlaceMachine.accessHooks config) resolvedNext finishNext = _
  have resolveStep := @resolve_write K U inferInstance config pointers canonical machine id tag base offset count capacity entry tree width positive signedFits
    cached present size bounds mutable synchronize before access signed nonzero resolved raw checked stored contains finishNext resolvedNext
  rw [resolveStep]
  change accessRaw machine.memory (PlaceMachine.AccessState.mk machine none) ⟨Size.ofBytes 8⟩
    ⟨id,(Size.ofBytes offset),.concrete tag⟩ (Size.ofBytes count) (Int.ofNat count.toNat)
    config.globalKind config.globalHooks true finishNext = _
  have rawStep := @raw_write K U inferInstance config pointers canonical machine id tag base offset count capacity entry tree width positive signedFits
    cached present size bounds mutable synchronize before access signed nonzero resolved raw checked stored contains finishNext
  rw [rawStep]
  exact @access_finish_write K U inferInstance config pointers canonical machine id tag base offset count capacity entry tree width positive signedFits
    cached present size bounds mutable synchronize before access signed nonzero resolved raw checked stored contains

#print axioms get_ptr_write_of_access


end DuplicatePrefix.S04ReturnWindowPointer
