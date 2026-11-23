import Miri.Verification.MemoryWP

/-! VC generation for a production copy access with symbolic state and Tree Borrows. -/
namespace MiriTests.Verification.MemoryWP

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter Miri.Verification Std.WP
open Miri.Verification.MemoryWP

set_option experimental.vcgen true

variable {K U : Type}
local notation "State" => MachineHooks.State K U

/-- A Tree Borrows failure bypasses synchronization and reports the copy state
after committing the tree left by the failed access. -/
example [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (allocation : Allocation Provenance BorrowTree) (id : AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange) (before : State)
    (diagnosed raced : MachineHooks.MachineState K U) (borrow : MachineHooks.BorrowState)
    (post : Allocation Provenance BorrowTree → State → Prop) (onError : StepError → State → Prop)
    (diagnostic : config.diagnostic false id range before.machine = .ok () diagnosed)
    (race : MachineHooks.memoryRaceAccess diagnosed id range none .Read = (raced, .ok ()))
    (tracked : raced.borrowTracker = some borrow)
    (tree :
      TreeBorrowsWP.accessPre allocation.extra provenance range.start range.size .Read
        borrow.global.protectedTags .VisitChildrenOfAccessed
        (fun updated _ =>
          wp (config.syncAccess false id range)
            (fun _ synced =>
              copyAccessCommitPre config before allocation id range ⟨synced, none⟩ updated
                (.ok ()) post onError)
            (fun error failed =>
              copyAccessCommitPre config before allocation id range ⟨failed, some error⟩ updated
                (.error (reprStr error)) post onError) raced)
        (fun status updated _ =>
          let error := PlaceMachine.treeError false status
          copyAccessCommitPre config before allocation id range ⟨raced, some error⟩ updated
            (.error (reprStr error)) post onError)) :
    Triple (GlobalMemoryCopyMachine.access config false allocation id provenance range)
      (· = before) post onError := by
  vcgen
  rename_i state entry
  subst state
  simpa only [memoryAccessPre, policyPre, failurePre, reprStr, wp, WP.wpTrans, diagnostic, race, tracked,
    Bool.false_eq_true, ↓reduceIte] using tree

/-- A scalar-pair write reaches the selected pointer's actual Tree
Borrows stage and carries the resulting cache into both byte mutations. -/
example [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (later : MemoryOperandLayout → Bool) (first second : Scalar Provenance) (place : MPlaceTy Provenance)
    (before : State) (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (checked : CheckedPlaceAccess config true before.machine.memory ⟨before.machine, none⟩
      ⟨place.mplace, localMemoryLayout place.layout⟩)
    (sized : (localMemoryLayout place.layout).backendRepr.isUnsized = false)
    (abi : immediateMatchesAbi (.scalarPair first second) (localMemoryLayout place.layout) config.runtime = .ok ())
    (checkedWrite : checked.pre (fun selected =>
      resultPre config before (writeImmediateAfterAccess (.scalarPair first second) (localMemoryLayout place.layout)
        config.runtime later selected) post onError)) :
    Triple (PlaceMachine.writeMemory config later (.scalarPair first second) place)
      (· = before) post onError := by
  vcgen
  rename_i state entry
  subst state
  rw [immediateWritePre_iff, writeMemory_iff]
  exact (immediateWrite_resultPre_iff config later (.scalarPair first second) place post onError before
    checked sized abi).mpr checkedWrite

/-- A scalar read uses the updated allocation and still checks the loaded
bytes before discharging its successful continuation. -/
example [DecidableEq K] (config : PlaceMachine.AccessConfig K U) (operand : OpTy Provenance)
    (mplace : MemPlace Provenance) (primitive : BackendPrimitive) (validRange : WrappingRange)
    (before : State) (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop)
    (checked : CheckedPlaceAccess config false before.machine.memory ⟨before.machine, none⟩
      ⟨mplace, localMemoryLayout operand.layout⟩)
    (indirect : operand.op = .indirect mplace)
    (backend : (localMemoryLayout operand.layout).backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := validRange)))
    (width : primitive.size config.runtime = .ok (localMemoryLayout operand.layout).size)
    (checkedRead : checked.pre (fun selected =>
      resultPre config before
        (scalarReadAfterAccess (localMemoryLayout operand.layout) primitive config.runtime selected)
        (fun value => post ⟨value.value, operand.layout⟩) onError)) :
    Triple (PlaceMachine.readImmediate config operand) (· = before) post onError := by
  vcgen
  rename_i state entry
  subst state
  rw [immediateReadPre_iff, readImmediate_iff]
  exact (scalarRead_resultPre_iff config operand mplace primitive validRange post onError before
    checked indirect backend width).mpr checkedRead

/-- A scalar-pair load reaches the same exact access stage and its two
component reads use the resulting allocation. -/
example [DecidableEq K] (config : PlaceMachine.AccessConfig K U) (operand : OpTy Provenance)
    (mplace : MemPlace Provenance) (left right : BackendPrimitive)
    (leftRange rightRange : WrappingRange) (offset : Size)
    (before : State) (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop)
    (checked : CheckedPlaceAccess config false before.machine.memory ⟨before.machine, none⟩
      ⟨mplace, localMemoryLayout operand.layout⟩)
    (indirect : operand.op = .indirect mplace)
    (backend : (localMemoryLayout operand.layout).backendRepr =
      .ScalarPair (a := .Initialized (value := left) (validRange := leftRange))
        (b := .Initialized (value := right) (validRange := rightRange)) (bOffset := offset))
    (checkedRead : checked.pre (fun selected =>
      resultPre config before
        (finishImmediateRead (finishRawOperandRead ⟨mplace, localMemoryLayout operand.layout⟩
          (readImmediateAfterAccess (localMemoryLayout operand.layout) config.runtime selected)))
        (fun value => post ⟨value.value, operand.layout⟩) onError)) :
    Triple (PlaceMachine.readImmediate config operand) (· = before) post onError := by
  vcgen
  rename_i state entry
  subst state
  have sized : (localMemoryLayout operand.layout).backendRepr.isUnsized = false := by
    rw [backend]
    rfl
  have readable : isPrimitiveReadable (localMemoryLayout operand.layout).backendRepr = true := by
    rw [backend]
    rfl
  rw [immediateReadPre_iff, readImmediate_iff]
  exact (immediateRead_resultPre_iff config operand mplace post onError before
    checked indirect sized readable).mpr checkedRead

/-- An indirect operand read retains the raw place fallback and can hand the
resulting state to the physical copy path. -/
example [DecidableEq K] (config : PlaceMachine.AccessConfig K U) (operand : OpTy Provenance)
    (mplace : MemPlace Provenance) (before : State)
    (post : ImmediateOrPlace Provenance → State → Prop) (onError : StepError → State → Prop)
    (checked : CheckedPlaceAccess config false before.machine.memory ⟨before.machine, none⟩
      ⟨mplace, localMemoryLayout operand.layout⟩)
    (indirect : operand.op = .indirect mplace)
    (sized : (localMemoryLayout operand.layout).backendRepr.isUnsized = false)
    (checkedRead : checked.pre (fun selected => resultPre config before
      (finishRawOperandRead ⟨mplace, localMemoryLayout operand.layout⟩
        (readImmediateAfterAccess (localMemoryLayout operand.layout) config.runtime selected))
      post onError)) :
    Triple (PlaceMachine.readRaw config operand) (· = before) post onError := by
  vcgen
  rename_i state entry
  subst state
  rw [rawOperandPre_iff]
  exact (rawRead_resultPre_iff config operand mplace post onError before
    checked indirect sized).mpr checkedRead

/-- Full-place uninitialization uses the dynamic size and preserves the
metadata resolution state when checking Tree Borrows. -/
example [DecidableEq K] (config : PlaceMachine.AccessConfig K U) (place : MPlaceTy Provenance)
    (before : State) (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (afterMemory : MemoryState Provenance BorrowTree K) (afterHooks : PlaceMachine.AccessState K U)
    (size : Size) (align : Align)
    (resolved : config.dynamicLayout before.machine.memory ⟨before.machine, none⟩
      ⟨place.mplace, localMemoryLayout place.layout⟩ = ⟨afterMemory, afterHooks, .ok (some (size, align))⟩)
    (checked : CheckedPlaceAccess config true afterMemory afterHooks
      ⟨place.mplace, {(localMemoryLayout place.layout) with size, align}⟩)
    (unsized : (localMemoryLayout place.layout).backendRepr.isUnsized = true)
    (checkedWrite : checked.pre (fun selected =>
      resultPre config before (uninitWriteAfterAccess config.runtime.pointerSize selected) post onError)) :
    Triple (PlaceMachine.writeUninitMemory config place) (· = before) post onError := by
  vcgen
  rename_i state entry
  subst state
  rw [uninitWritePre_iff, writeUninitMemory_iff]
  exact (writeUninit_dynamic_resultPre_iff config place post onError before afterMemory afterHooks
    size align resolved checked unsized).mpr checkedWrite

/-- The immediate-local path threads the updated frame directly into the
local race hook and ABI checker. -/
example {P S E : Type} (getFrame : PlaceM S (Frame P LocalLayout E))
    (setFrame : Frame P LocalLayout E → PlaceM S Unit) (validationInProgress : PlaceM S Bool)
    (afterLocalWrite : Miri.MIR.LocalId → Bool → PlaceM S Unit)
    (debugAbiCheck : Immediate P → LocalLayout → PlaceM S Unit)
    (id : Miri.MIR.LocalId) (layout : LocalLayout) (old value : Immediate P)
    (post : Unit → S → Prop) (onError : StepError → S → Prop)
    (before current : S) (frame updated : Frame P LocalLayout E)
    (sized : layout.layout.isSized = true)
    (loaded : getFrame before = .ok frame current)
    (localValue : frame.getLocalOperand id = .ok (.immediate old))
    (written : frame.setLocalOperand id (.immediate value) = .ok updated)
    (checked : wp (do
      setFrame updated
      unless ← validationInProgress do afterLocalWrite id false
      debugAbiCheck value layout) post onError current) :
    Triple (placeWriteLocalImmediate getFrame setFrame validationInProgress afterLocalWrite
        debugAbiCheck id layout value) (· = before) post onError := by
  apply Triple.iff.mpr
  intro state entry
  subst state
  exact (localImmediateWrite_iff getFrame setFrame validationInProgress afterLocalWrite debugAbiCheck
    id layout old value post onError before current frame updated sized loaded localValue written).mpr checked

local notation "HookState" => PlaceMachine.AccessState K U
local notation "PtrResult" => PtrAllocationResult Provenance BorrowTree K HookState
  (Option (AllocationAccessRef Provenance BorrowTree))

/-- A nonzero unlinked pointer reports the exact integer address and the
state produced by resolution, before attempting raw lookup. -/
example [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (memory : MemoryState Provenance BorrowTree K) (hooks afterHooks : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Provenance)) (size : Size)
    (amount : Int) (address : UInt64) (post : PtrResult → Prop)
    (signed : sizeAsI64 size = .ok amount) (nonzero : amount ≠ 0)
    (resolve : (PlaceMachine.accessHooks config).resolvePointer memory hooks ptr amount =
      ⟨afterHooks, .ok (.error address)⟩) :
    pointerAccessPre config true memory hooks target ptr size post ↔
      post ⟨memory, afterHooks, none, .error (.access (.danglingIntegerPointer address amount .memoryAccess))⟩ := by
  simp [pointerAccessPre, AllocationAccess.preparePtrAllocation, signed, nonzero, resolve]

/-- Failed raw lookup can retain state from global materialization. -/
example [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (memory rawMemory : MemoryState Provenance BorrowTree K)
    (hooks resolvedHooks rawHooks : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Provenance)) (size : Size)
    (amount : Int) (resolved : ResolvedPointer ProvenanceExtra)
    (failure : MemoryAccessError) (post : PtrResult → Prop)
    (signed : sizeAsI64 size = .ok amount) (nonzero : amount ≠ 0)
    (resolve : (PlaceMachine.accessHooks config).resolvePointer memory hooks ptr amount =
      ⟨resolvedHooks, .ok (.ok resolved)⟩)
    (raw : MemoryLifecycle.getAllocRawMut memory resolvedHooks resolved.allocId config.globalKind
      config.globalHooks = ⟨rawMemory, rawHooks, .error failure⟩) :
    pointerAccessPre config true memory hooks target ptr size post ↔
      post ⟨rawMemory, rawHooks, none, .error (.rawAccess failure)⟩ := by
  simp [pointerAccessPre, AllocationAccess.preparePtrAllocation, signed, nonzero, resolve, raw]

/-- Bounds rejection keeps the acquired allocation snapshot but does not
run the memory hook. -/
example [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (memory rawMemory : MemoryState Provenance BorrowTree K)
    (hooks resolvedHooks rawHooks : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Provenance)) (size : Size)
    (amount : Int) (resolved : ResolvedPointer ProvenanceExtra)
    (allocation : Allocation Provenance BorrowTree) (failure : AccessError) (post : PtrResult → Prop)
    (signed : sizeAsI64 size = .ok amount) (nonzero : amount ≠ 0)
    (resolve : (PlaceMachine.accessHooks config).resolvePointer memory hooks ptr amount =
      ⟨resolvedHooks, .ok (.ok resolved)⟩)
    (raw : MemoryLifecycle.getAllocRawMut memory resolvedHooks resolved.allocId config.globalKind
      config.globalHooks = ⟨rawMemory, rawHooks, .ok allocation⟩)
    (bounds : checkedBounds target resolved.allocId allocation.byteSize resolved.offset amount .memoryAccess =
      .error failure) :
    pointerAccessPre config true memory hooks target ptr size post ↔
      post ⟨rawMemory, rawHooks, some ⟨resolved.allocId, allocRange resolved.offset size, allocation⟩,
        .error (.access failure)⟩ := by
  simp [pointerAccessPre, AllocationAccess.preparePtrAllocation, signed, nonzero, resolve, raw, bounds]

/-- The zero-sized read probes the address but succeeds without an
allocation on an unresolved integer pointer. -/
example [DecidableEq K] (config : PlaceMachine.AccessConfig K U)
    (memory : MemoryState Provenance BorrowTree K) (hooks afterHooks : HookState)
    (target : PointerArithmetic) (ptr : Pointer (Option Provenance)) (size : Size)
    (address : UInt64) (post : PtrResult → Prop)
    (signed : sizeAsI64 size = .ok 0) (notGhost : config.ghostMode = false)
    (resolve : (PlaceMachine.accessHooks config).resolvePointer memory hooks ptr 0 =
      ⟨afterHooks, .ok (.error address)⟩) :
    pointerAccessPre config false memory hooks target ptr size post ↔
      post ⟨memory, afterHooks, none, .ok none⟩ := by
  simp [pointerAccessPre, AllocationAccess.preparePtrAllocation, signed, notGhost, resolve]

end MiriTests.Verification.MemoryWP
