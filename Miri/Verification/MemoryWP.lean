import Miri.Interpreter.GlobalMemoryCopyMachine
import Miri.Interpreter.OperandMachine
import Miri.Verification.EffectSpecs
import Miri.Verification.TreeBorrowsWP

/-! Exact weakest preconditions for the machine's typed memory operations. -/
namespace Miri.Verification.MemoryWP

open Miri.ABI Miri.Memory Miri.TreeBorrows Miri.Interpreter Std.WP

variable {K U A : Type}
local notation "State" => MachineHooks.State K U
local notation "Config" => PlaceMachine.AccessConfig K U
local notation "HookState" => PlaceMachine.AccessState K U
local notation "Result" => MemoryOperandResult Provenance BorrowTree K (PlaceMachine.AccessState K U)

/-- The memory bridge commits the actual allocation snapshot on both exits.
The hook's pending typed error takes precedence over the memory error. -/
def resultPre (config : Config) (before : State) (result : Result A)
    (post : A → State → Prop) (onError : StepError → State → Prop) : Prop :=
  let machine := {result.hooks.machine with memory := result.memory}
  let after := {before with machine := config.retainTouched machine result.touched}
  match result.outcome with
  | .ok value => post value after
  | .error error => onError (result.hooks.pendingError.getD (config.memoryError error)) after

/-- Checked operand reads compose with a value continuation using exactly the
state from raw access. In particular, immediate initialization checks can
fail after a successful allocation access. -/
theorem readImmediate_iff [DecidableEq K] (config : Config) (operand : OpTy Provenance)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop)
    (before : State) :
    wp (PlaceMachine.readImmediate config operand) post onError before ↔
      resultPre config before
        (Miri.Interpreter.readImmediate before.machine.memory ⟨before.machine, none⟩ operand.op
          (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
          config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout)
        (fun value => post ⟨value.value, operand.layout⟩) onError := by
  simp only [wp, WP.wpTrans, resultPre, PlaceMachine.readImmediate, get, getThe, MonadStateOf.get,
    EStateM.get, bind, Bind.bind, EStateM.bind, PlaceMachine.commit,
    PlaceMachine.finish, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  generalize Miri.Interpreter.readImmediate before.machine.memory ⟨before.machine, none⟩ operand.op
    (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
    config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = result
  cases outcome : result.outcome <;> rfl

@[spec low] theorem spec_readImmediate [DecidableEq K] (config : Config)
    (operand : OpTy Provenance) (post : RvalueImmTy Provenance → State → Prop)
    (onError : StepError → State → Prop) :
    Triple (PlaceMachine.readImmediate config operand)
      (fun before => resultPre config before
        (Miri.Interpreter.readImmediate before.machine.memory ⟨before.machine, none⟩ operand.op
          (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
          config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout)
        (fun value => post ⟨value.value, operand.layout⟩) onError) post onError :=
  Triple.iff.mpr (fun before => (readImmediate_iff config operand post onError before).mpr)

theorem readRaw_iff [DecidableEq K] (config : Config) (operand : OpTy Provenance)
    (post : ImmediateOrPlace Provenance → State → Prop) (onError : StepError → State → Prop)
    (before : State) :
    wp (PlaceMachine.readRaw config operand) post onError before ↔
      resultPre config before
        (readImmediateRaw before.machine.memory ⟨before.machine, none⟩ operand.op
          (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
          config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout)
        post onError := by
  simp only [wp, WP.wpTrans, resultPre, PlaceMachine.readRaw, get, getThe, MonadStateOf.get,
    EStateM.get, bind, Bind.bind, EStateM.bind, PlaceMachine.commit,
    PlaceMachine.finish, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  generalize readImmediateRaw before.machine.memory ⟨before.machine, none⟩ operand.op
    (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
    config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = result
  cases outcome : result.outcome <;> rfl

@[spec low] theorem spec_readRaw [DecidableEq K] (config : Config) (operand : OpTy Provenance)
    (post : ImmediateOrPlace Provenance → State → Prop) (onError : StepError → State → Prop) :
    Triple (PlaceMachine.readRaw config operand)
      (fun before => resultPre config before
        (readImmediateRaw before.machine.memory ⟨before.machine, none⟩ operand.op
          (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
          config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout)
        post onError) post onError :=
  Triple.iff.mpr (fun before => (readRaw_iff config operand post onError before).mpr)

theorem writeMemory_iff [DecidableEq K] (config : Config)
    (willValidate : MemoryOperandLayout → Bool) (value : Immediate Provenance)
    (place : MPlaceTy Provenance) (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (before : State) :
    wp (PlaceMachine.writeMemory config willValidate value place) post onError before ↔
      resultPre config before
        (writeImmediateToMplaceNoValidate before.machine.memory ⟨before.machine, none⟩ value
          ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
          config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout willValidate)
        post onError := by
  simp only [wp, WP.wpTrans, resultPre, PlaceMachine.writeMemory, get, getThe, MonadStateOf.get,
    EStateM.get, bind, Bind.bind, EStateM.bind, PlaceMachine.commit,
    PlaceMachine.finish, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  generalize writeImmediateToMplaceNoValidate before.machine.memory ⟨before.machine, none⟩ value
    ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
    config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout willValidate = result
  cases outcome : result.outcome <;> rfl

@[spec low] theorem spec_writeMemory [DecidableEq K] (config : Config)
    (willValidate : MemoryOperandLayout → Bool) (value : Immediate Provenance)
    (place : MPlaceTy Provenance) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (PlaceMachine.writeMemory config willValidate value place)
      (fun before => resultPre config before
        (writeImmediateToMplaceNoValidate before.machine.memory ⟨before.machine, none⟩ value
          ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
          config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout willValidate)
        post onError) post onError :=
  Triple.iff.mpr (fun before => (writeMemory_iff config willValidate value place post onError before).mpr)

theorem writeUninitMemory_iff [DecidableEq K] (config : Config)
    (place : MPlaceTy Provenance) (post : Unit → State → Prop) (onError : StepError → State → Prop)
    (before : State) :
    wp (PlaceMachine.writeUninitMemory config place) post onError before ↔
      resultPre config before
        (writeUninitToMplace before.machine.memory ⟨before.machine, none⟩
          ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
          config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout)
        post onError := by
  simp only [wp, WP.wpTrans, resultPre, PlaceMachine.writeUninitMemory, get, getThe, MonadStateOf.get,
    EStateM.get, bind, Bind.bind, EStateM.bind, PlaceMachine.commit,
    PlaceMachine.finish, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]
  generalize writeUninitToMplace before.machine.memory ⟨before.machine, none⟩
    ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
    config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout = result
  cases outcome : result.outcome <;> rfl

@[spec low] theorem spec_writeUninitMemory [DecidableEq K] (config : Config)
    (place : MPlaceTy Provenance) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (PlaceMachine.writeUninitMemory config place)
      (fun before => resultPre config before
        (writeUninitToMplace before.machine.memory ⟨before.machine, none⟩
          ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
          config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout)
        post onError) post onError :=
  Triple.iff.mpr (fun before => (writeUninitMemory_iff config place post onError before).mpr)

attribute [spec] OperandMachine.localToOp OperandMachine.field
attribute [spec] PlaceMachine.layoutLocal PlaceMachine.localToOpCore PlaceMachine.localToOp
attribute [spec] writePlaceImmediate writePlaceImmediateNoValidate forceAllocation
attribute [spec] asMplaceOrMutableLocal placeWriteLocalImmediate
attribute [spec] MachineHooks.afterLocalRead MachineHooks.afterLocalWrite
attribute [spec] copyRuntimePlaceNoValidate GlobalMemoryCopyMachine.typedCopy
attribute [spec] DynamicLayout.sizeAndAlignFromMeta

/-- Pull back through a memory hook while retaining its updated tree and
typed pending error. The error string also survives the allocation layer. -/
def accessResultPre (result : AllocationExtraHookResult HookState BorrowTree)
    (post : HookState → BorrowTree → Prop)
    (onError : String → HookState → BorrowTree → Prop) : Prop :=
  match result.outcome with
  | .ok () => post result.state result.extra
  | .error message => onError message result.state result.extra

/-- Pull back through a diagnostic, weak-memory or synchronization policy.
All three use the same bridge between the typed machine error and the raw
allocation error string. -/
def policyPre (action : PlaceMachine.MachineM K U Unit)
    (before : HookState) (tree : BorrowTree)
    (post : HookState → BorrowTree → Prop)
    (onError : String → HookState → BorrowTree → Prop) : Prop :=
  wp action (fun _ machine => post {before with machine} tree)
    (fun error machine => onError (reprStr error) ⟨machine, some error⟩ tree) before.machine

/-- Deliver a typed access failure with the exact hook error and tree state. -/
def failurePre (error : StepError) (state : HookState) (tree : BorrowTree)
    (onError : String → HookState → BorrowTree → Prop) : Prop :=
  onError (reprStr error) {state with pendingError := some error} tree

private theorem treeBranch_iff (tree : BorrowTree)
    (provenance : ProvenanceExtra) (range : AllocRange) (kind : AccessKind) (tags : ProtectedTags)
    (post : BorrowTree → Prop) (onError : BorrowTree.BorrowTreeAccessStatus → BorrowTree → Prop) :
    TreeBorrowsWP.accessPre tree provenance range.start range.size kind tags .VisitChildrenOfAccessed
      (fun updated _ => post updated) (fun status updated _ => onError status updated) ↔
    (let access := tree.performBorrowAccessRange provenance range.start range.size kind tags .VisitChildrenOfAccessed
     if access.status != .Completed then onError access.status access.tree
     else post access.tree) := by
  rw [TreeBorrowsWP.accessPre_iff]
  dsimp only
  generalize tree.performBorrowAccessRange provenance range.start range.size
    kind tags .VisitChildrenOfAccessed = result
  cases result with
  | mk _ _ status => cases status <;> rfl

/-- State and tree continuations for a non-atomic typed access in source order.
A failed race check precedes any TB action. A failed TB action exposes the
tree reached by its partial traversal and bypasses synchronization. -/
def memoryAccessPre (config : Config) (write : Bool) (before : HookState)
    (tree : BorrowTree) (id : AllocId) (provenance : ProvenanceExtra) (range : AllocRange)
    (post : HookState → BorrowTree → Prop)
    (onError : String → HookState → BorrowTree → Prop) : Prop :=
  let sync := fun state currentTree =>
    policyPre (config.syncAccess write id range) state currentTree post onError
  let borrow := fun state currentTree =>
    match state.machine.borrowTracker with
    | none => sync state currentTree
    | some tracker =>
      TreeBorrowsWP.accessPre currentTree provenance range.start range.size
        (if write then .Write else .Read) tracker.global.protectedTags .VisitChildrenOfAccessed
        (fun updated _ => sync state updated)
        (fun status updated _ => failurePre (PlaceMachine.treeError write status) state updated onError)
  policyPre (config.diagnostic write id range) before tree
    (fun state currentTree =>
      let (machine, race) := MachineHooks.memoryRaceAccess state.machine id range
        (if write then some .Write else none) .Read
      let state := {state with machine}
      match race with
      | .error error => failurePre error state currentTree onError
      | .ok () =>
        if write then policyPre (config.weakMemoryWrite id range) state currentTree borrow onError
        else borrow state currentTree) onError

theorem memoryAccess_iff (config : Config) (write : Bool) (before : HookState)
    (tree : BorrowTree) (id : AllocId) (provenance : ProvenanceExtra) (range : AllocRange)
    (post : HookState → BorrowTree → Prop)
    (onError : String → HookState → BorrowTree → Prop) :
    accessResultPre (PlaceMachine.memoryAccess config write before tree id provenance range) post onError ↔
      memoryAccessPre config write before tree id provenance range post onError := by
  simp only [PlaceMachine.memoryAccess, memoryAccessPre, treeBranch_iff, policyPre,
    failurePre, wp, WP.wpTrans,
    Id.run, pure, Pure.pure, PlaceMachine.bridge]
  cases diagnostic : config.diagnostic write id range before.machine
  · rename_i value machine
    cases value
    rcases race : MachineHooks.memoryRaceAccess machine id range
        (if write then some .Write else none) .Read with ⟨raced, outcome⟩
    cases outcome with
    | error error => simp only [race]; rfl
    | ok value =>
      cases value
      simp only [race]
      cases write
      · simp only [Bool.false_eq_true, ↓reduceIte]
        cases raced.borrowTracker with
        | none => cases config.syncAccess false id range raced <;> rfl
        | some tracker =>
          by_cases status :
              ((tree.performBorrowAccessRange provenance range.start range.size .Read
                tracker.global.protectedTags .VisitChildrenOfAccessed).status != .Completed) = true
          · simp [status, accessResultPre]
          · cases config.syncAccess false id range raced <;> simp [status, accessResultPre]
      · simp only [↓reduceIte]
        cases weak : config.weakMemoryWrite id range raced with
        | error error machine => rfl
        | ok value weakMachine =>
          cases value
          simp only
          cases weakMachine.borrowTracker with
          | none => cases config.syncAccess true id range weakMachine <;> rfl
          | some tracker =>
            by_cases status :
                ((tree.performBorrowAccessRange provenance range.start range.size .Write
                  tracker.global.protectedTags .VisitChildrenOfAccessed).status != .Completed) = true
            · simp [status, accessResultPre]
            · cases config.syncAccess true id range weakMachine <;> simp [status, accessResultPre]
  · rfl

/-- A caller of an allocation hook can pull any continuation on the
complete raw result back through its memory-access stages. This applies
inside an operand rule that has already selected its allocation and range,
including continuations that cache the updated extra before observing failure. -/
theorem memoryAccess_context_iff (config : Config) (write : Bool) (before : HookState)
    (tree : BorrowTree) (id : AllocId) (provenance : ProvenanceExtra) (range : AllocRange)
    (continuation : AllocationExtraHookResult HookState BorrowTree → Prop) :
    continuation (PlaceMachine.memoryAccess config write before tree id provenance range) ↔
      memoryAccessPre config write before tree id provenance range
        (fun state tree => continuation ⟨state, tree, .ok ()⟩)
        (fun message state tree => continuation ⟨state, tree, .error message⟩) := by
  rw [← memoryAccess_iff]
  generalize PlaceMachine.memoryAccess config write before tree id provenance range = result
  rcases result with ⟨_, _, ⟨⟨⟩⟩ | ⟨_⟩⟩ <;> rfl

/-- After a copy access, synchronize the updated allocation extra before
propagating a hook failure. A cache failure instead leaves the original
machine state and overrides the pending hook error. -/
def copyAccessCommitPre [DecidableEq K] (config : Config)
    (before : MachineHooks.State K U) (allocation : Allocation Provenance BorrowTree)
    (id : AllocId) (range : AllocRange) (state : HookState) (tree : BorrowTree)
    (outcome : Except String Unit)
    (post : Allocation Provenance BorrowTree → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) : Prop :=
  let updated := allocation.setExtra tree
  let machine := state.machine
  let result :=
    if machine.memory.live.any (fun entry => entry.1 == id) then
      machine.memory.setLiveAllocation id updated
    else .ok machine.memory
  match result with
  | .error error => onError (config.memoryError (.memoryUpdate error)) before
  | .ok memory =>
    let machine := config.retainTouched {machine with memory} (some ⟨id, range, updated⟩)
    let after := {before with machine}
    match outcome with
    | .ok () => post updated after
    | .error message => onError (state.pendingError.getD (.callback message)) after

theorem copyAccess_iff [DecidableEq K] (config : Config) (write : Bool)
    (allocation : Allocation Provenance BorrowTree) (id : AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange)
    (post : Allocation Provenance BorrowTree → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) (before : MachineHooks.State K U) :
    wp (GlobalMemoryCopyMachine.access config write allocation id provenance range) post onError before ↔
      memoryAccessPre config write ⟨before.machine, none⟩ allocation.extra id provenance range
        (fun state tree => copyAccessCommitPre config before allocation id range state tree
          (.ok ()) post onError)
        (fun message state tree => copyAccessCommitPre config before allocation id range state tree
          (.error message) post onError) := by
  rw [← memoryAccess_iff]
  simp only [wp, WP.wpTrans, GlobalMemoryCopyMachine.access, accessResultPre, copyAccessCommitPre,
    get, getThe, MonadStateOf.get, EStateM.get, bind, Bind.bind, EStateM.bind]
  generalize PlaceMachine.memoryAccess config write ⟨before.machine, none⟩ allocation.extra
    id provenance range = result
  cases result with
  | mk state tree outcome =>
    rcases outcome with ⟨⟨⟩⟩ | ⟨error⟩ <;>
      by_cases live : (state.machine.memory.live.any (fun entry => entry.1 == id)) = true <;>
      simp only [live, ↓reduceIte] <;>
      (try cases state.machine.memory.setLiveAllocation id (allocation.setExtra tree)) <;>
      rfl

@[spec] theorem spec_copyAccess [DecidableEq K] (config : Config) (write : Bool)
    (allocation : Allocation Provenance BorrowTree) (id : AllocId)
    (provenance : ProvenanceExtra) (range : AllocRange)
    (post : Allocation Provenance BorrowTree → MachineHooks.State K U → Prop)
    (onError : StepError → MachineHooks.State K U → Prop) :
    Triple (GlobalMemoryCopyMachine.access config write allocation id provenance range)
      (fun before =>
        memoryAccessPre config write ⟨before.machine, none⟩ allocation.extra id provenance range
          (fun state tree => copyAccessCommitPre config before allocation id range state tree
            (.ok ()) post onError)
          (fun message state tree => copyAccessCommitPre config before allocation id range state tree
            (.error message) post onError)) post onError :=
  Triple.iff.mpr (fun before => (copyAccess_iff config write allocation id provenance range
    post onError before).mpr)

local notation "Memory" => MemoryState Provenance BorrowTree K
local notation "Reference" => AllocationAccessRef Provenance BorrowTree

local notation "PointerResult" => PtrAllocationResult Provenance BorrowTree K HookState (Option Reference)

/-- Interpret both outcomes of the actual allocation preparation. A finished
result already contains any resolver, global cache, or before-allocation
effects. The access path exposes Tree Borrows before committing the extra. -/
def pointerAccessPre [DecidableEq K] (config : Config) (write : Bool)
    (memory : Memory) (hooks : HookState) (target : PointerArithmetic)
    (ptr : Pointer (Option Provenance)) (size : Size)
    (post : PointerResult → Prop) : Prop :=
  match AllocationAccess.preparePtrAllocation memory hooks target ptr size config.ghostMode
      config.globalKind config.globalHooks (PlaceMachine.accessHooks config) write with
  | .finished result => post result
  | .access memory hooks provenance reference =>
    memoryAccessPre config write hooks reference.allocation.extra reference.allocId provenance reference.range
      (fun state tree => post (AllocationAccess.finishCheckedAccess write memory reference ⟨state, tree, .ok ()⟩))
      (fun error state tree => post (AllocationAccess.finishCheckedAccess write memory reference ⟨state, tree, .error error⟩))

theorem pointerAccessPre_iff [DecidableEq K] (config : Config) (write : Bool)
    (memory : Memory) (hooks : HookState) (target : PointerArithmetic)
    (ptr : Pointer (Option Provenance)) (size : Size) (post : PointerResult → Prop) :
    pointerAccessPre config write memory hooks target ptr size post ↔
      post (AllocationAccess.getPtrAllocation memory hooks target ptr size config.ghostMode
        config.globalKind config.globalHooks (PlaceMachine.accessHooks config) write) := by
  unfold pointerAccessPre AllocationAccess.getPtrAllocation
  generalize AllocationAccess.preparePtrAllocation memory hooks target ptr size config.ghostMode
    config.globalKind config.globalHooks (PlaceMachine.accessHooks config) write = prepared
  cases prepared with
  | finished result => rfl
  | access memory hooks provenance reference =>
    cases write <;> exact (memoryAccess_context_iff config _ hooks reference.allocation.extra
      reference.allocId provenance reference.range (fun result =>
        post (AllocationAccess.finishCheckedAccess _ memory reference result))).symm

/-- Select the actual static or dynamic layout and check pointer metadata
before dispatching allocation access. Alignment remains a post-access check. -/
def placeAccessPre [DecidableEq K] (config : Config) (write : Bool)
    (memory : Memory) (hooks : HookState) (place : MemoryOperandPlace Provenance)
    (post : Result (Option Reference) → Prop) : Prop :=
  let (memory, hooks, layout) := selectedSizeAndAlign memory hooks place config.dynamicLayout
  match layout with
  | .error error => post ⟨memory, hooks, none, .error error⟩
  | .ok (size, _) =>
    match pointerArithmeticFor config.runtime with
    | .error error => post ⟨memory, hooks, none, .error error⟩
    | .ok target =>
      pointerAccessPre config write memory hooks target place.mplace.ptr size
        (fun result => post (finishPlaceAccess result place.mplace.misaligned))

theorem placeAccessPre_iff [DecidableEq K] (config : Config) (write : Bool)
    (memory : Memory) (hooks : HookState) (place : MemoryOperandPlace Provenance)
    (post : Result (Option Reference) → Prop) :
    placeAccessPre config write memory hooks place post ↔
      post (if write then getPlaceAllocMut memory hooks place config.runtime config.ghostMode config.globalKind
          config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
        else getPlaceAlloc memory hooks place config.runtime config.ghostMode config.globalKind
          config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout) := by
  cases write <;>
    simp only [placeAccessPre, getPlaceAlloc, getPlaceAllocMut, Bool.false_eq_true, ↓reduceIte,
      Id.run, bind, Bind.bind, pure, Pure.pure]
  all_goals
    rcases selectedSizeAndAlign memory hooks place config.dynamicLayout with ⟨selectedMemory,selectedHooks,layout⟩
    cases layout with
    | error error => rfl
    | ok pair =>
      rcases pair with ⟨size, align⟩
      cases pointerArithmeticFor config.runtime with
      | error error => rfl
      | ok target =>
        exact pointerAccessPre_iff config _ selectedMemory selectedHooks target place.mplace.ptr size _

set_option autoImplicit false in
/-- The metadata, pointer, allocation and bounds checks that select a genuine
nonzero access to a sized place outside ghost mode. A read's second resolution
is retained with its own resulting hook state. The raw lookup may materialize
globals and change the memory. -/
structure CheckedPlaceAccess [DecidableEq K] (config : Config) (write : Bool)
    (memory : Memory) (hooks : HookState) (place : MemoryOperandPlace Provenance) where
  pointerSize : Size
  runtimePointerSize : config.runtime.pointerSizeIn config.runtime.defaultAddressSpace = .ok pointerSize
  notGhost : config.ghostMode = false
  amount : Int
  signedSize : sizeAsI64 place.layout.size = .ok amount
  nonzero : amount ≠ 0
  resolved : ResolvedPointer ProvenanceExtra
  resolvedHooks : HookState
  resolution : (PlaceMachine.accessHooks config).resolvePointer memory hooks place.mplace.ptr amount =
    ⟨resolvedHooks, .ok (.ok resolved)⟩
  rawMemory : Memory
  rawHooks : HookState
  allocation : Allocation Provenance BorrowTree
  raw : (if write then MemoryLifecycle.getAllocRawMut memory resolvedHooks resolved.allocId
      config.globalKind config.globalHooks
    else MemoryLifecycle.getAllocRaw memory resolvedHooks resolved.allocId
      config.globalKind config.globalHooks) = ⟨rawMemory, rawHooks, .ok allocation⟩
  bounds : checkedBounds ⟨pointerSize⟩ resolved.allocId allocation.byteSize resolved.offset
    amount .memoryAccess = .ok ()
  probed : ResolvedPointer ProvenanceExtra
  probeHooks : HookState
  readProbe : write = false →
    (PlaceMachine.accessHooks config).resolvePointer rawMemory rawHooks place.mplace.ptr amount =
      ⟨probeHooks, .ok (.ok probed)⟩
  accessHooks : HookState
  beforeAccess : (PlaceMachine.accessHooks config).beforeAllocationAccess
    (if write then rawHooks else probeHooks)
    (if write then resolved.allocId else probed.allocId) = ⟨accessHooks, .ok ()⟩

/-- Pull a continuation back through the memory hook, cache commit, and the
place's delayed alignment check. -/
def CheckedPlaceAccess.pre [DecidableEq K] {config : Config} {write : Bool}
    {memory : Memory} {hooks : HookState} {place : MemoryOperandPlace Provenance}
    (checked : CheckedPlaceAccess config write memory hooks place)
    (post : Result (Option Reference) → Prop) : Prop :=
  let range := allocRange checked.resolved.offset place.layout.size
  let reference : Reference := ⟨checked.resolved.allocId, range, checked.allocation⟩
  let finish := fun access => post (finishPlaceAccess
    (AllocationAccess.finishCheckedAccess write checked.rawMemory reference access) place.mplace.misaligned)
  memoryAccessPre config write checked.accessHooks checked.allocation.extra checked.resolved.allocId
    checked.resolved.extra range
    (fun hooks tree => finish ⟨hooks, tree, .ok ()⟩)
    (fun error hooks tree => finish ⟨hooks, tree, .error error⟩)

theorem CheckedPlaceAccess.pre_iff_pointer [DecidableEq K] {config : Config} {write : Bool}
    {memory : Memory} {hooks : HookState} {place : MemoryOperandPlace Provenance}
    (checked : CheckedPlaceAccess config write memory hooks place)
    (post : Result (Option Reference) → Prop) :
    post (finishPlaceAccess
      (if write then AllocationAccess.getPtrAllocMut memory hooks ⟨checked.pointerSize⟩ place.mplace.ptr
          place.layout.size config.ghostMode config.globalKind config.globalHooks (PlaceMachine.accessHooks config)
        else AllocationAccess.getPtrAlloc memory hooks ⟨checked.pointerSize⟩ place.mplace.ptr
          place.layout.size config.ghostMode config.globalKind config.globalHooks (PlaceMachine.accessHooks config))
      place.mplace.misaligned) ↔ checked.pre post := by
  rw [checked.notGhost]
  rw [AllocationAccess.getPtrAlloc_checked write memory checked.rawMemory hooks checked.resolvedHooks
    checked.rawHooks checked.accessHooks ⟨checked.pointerSize⟩ place.mplace.ptr place.layout.size
    config.globalKind config.globalHooks (PlaceMachine.accessHooks config) checked.resolved checked.probed
    checked.allocation checked.amount checked.probeHooks checked.signedSize checked.nonzero
    checked.resolution checked.raw checked.bounds checked.readProbe checked.beforeAccess]
  unfold CheckedPlaceAccess.pre
  have callback : (if write then (PlaceMachine.accessHooks config).beforeMemoryWrite
      else (PlaceMachine.accessHooks config).beforeMemoryRead) checked.accessHooks
        checked.allocation.extra place.mplace.ptr checked.resolved.allocId checked.resolved.extra
        (allocRange checked.resolved.offset place.layout.size) =
      PlaceMachine.memoryAccess config write checked.accessHooks checked.allocation.extra
        checked.resolved.allocId checked.resolved.extra (allocRange checked.resolved.offset place.layout.size) := by
    cases write <;> rfl
  simp only [callback]
  let range := allocRange checked.resolved.offset place.layout.size
  let reference : Reference := ⟨checked.resolved.allocId, range, checked.allocation⟩
  exact memoryAccess_context_iff config write checked.accessHooks checked.allocation.extra
    checked.resolved.allocId checked.resolved.extra range (fun access =>
      post (finishPlaceAccess (AllocationAccess.finishCheckedAccess write checked.rawMemory reference access)
        place.mplace.misaligned))

theorem CheckedPlaceAccess.pre_iff [DecidableEq K] {config : Config} {write : Bool}
    {memory : Memory} {hooks : HookState} {place : MemoryOperandPlace Provenance}
    (checked : CheckedPlaceAccess config write memory hooks place)
    (sized : place.layout.backendRepr.isUnsized = false)
    (post : Result (Option Reference) → Prop) :
    post (if write then getPlaceAllocMut memory hooks place config.runtime config.ghostMode config.globalKind
        config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
      else getPlaceAlloc memory hooks place config.runtime config.ghostMode config.globalKind
        config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout) ↔ checked.pre post := by
  rw [sizedPlaceAccess write memory hooks place config.runtime checked.pointerSize config.ghostMode
    config.globalKind config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout
    sized checked.runtimePointerSize]
  exact checked.pre_iff_pointer post

/-- Refine a typed immediate write VC once the address and ABI checks have
selected the access. The continuation covers scalars, pairs, and uninit. -/
theorem immediateWrite_resultPre_iff [DecidableEq K] (config : Config)
    (later : MemoryOperandLayout → Bool) (value : Immediate Provenance) (place : MPlaceTy Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) (before : State)
    (checked : CheckedPlaceAccess config true before.machine.memory ⟨before.machine, none⟩
      ⟨place.mplace, localMemoryLayout place.layout⟩)
    (sized : (localMemoryLayout place.layout).backendRepr.isUnsized = false)
    (abi : immediateMatchesAbi value (localMemoryLayout place.layout) config.runtime = .ok ()) :
    resultPre config before
      (writeImmediateToMplaceNoValidate before.machine.memory ⟨before.machine, none⟩ value
        ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
        config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout later)
        post onError ↔
    checked.pre (fun selected =>
      resultPre config before
        (writeImmediateAfterAccess value (localMemoryLayout place.layout) config.runtime later selected)
        post onError) := by
  rw [immediateWrite_eq_afterAccess _ _ _ _ _ _ _ _ _ _ _ sized abi]
  simpa only [↓reduceIte] using checked.pre_iff sized
    (fun selected => resultPre config before
      (writeImmediateAfterAccess value (localMemoryLayout place.layout) config.runtime later selected)
      post onError)

/-- An immediate operand bypasses allocation access. The raw reader still
uses the concrete retention policy with an empty touched snapshot. -/
theorem readRaw_immediate_iff [DecidableEq K] (config : Config) (operand : OpTy Provenance)
    (value : Immediate Provenance)
    (post : ImmediateOrPlace Provenance → State → Prop) (onError : StepError → State → Prop)
    (before : State) (immediate : operand.op = .immediate value) :
    wp (PlaceMachine.readRaw config operand) post onError before ↔
      post (.immediate ⟨value, localMemoryLayout operand.layout⟩)
        {before with machine := config.retainTouched before.machine none} := by
  rw [readRaw_iff, immediate]
  rfl

/-- Raw reads of unsized indirect operands leave the bytes untouched and
pass the original place to the copy continuation. -/
theorem readRaw_unsized_iff [DecidableEq K] (config : Config) (operand : OpTy Provenance)
    (mplace : MemPlace Provenance)
    (post : ImmediateOrPlace Provenance → State → Prop) (onError : StepError → State → Prop)
    (before : State) (indirect : operand.op = .indirect mplace)
    (unsized : (localMemoryLayout operand.layout).backendRepr.isUnsized = true) :
    wp (PlaceMachine.readRaw config operand) post onError before ↔
      post (.place ⟨mplace, localMemoryLayout operand.layout⟩)
        {before with machine := config.retainTouched before.machine none} := by
  rw [readRaw_iff, indirect]
  simp only [readImmediateRaw, readImmediateFromMplaceRaw, unsized, ↓reduceIte,
    finishRawOperandRead, resultPre, Id.run, pure, Pure.pure]

/-- Refine the raw indirect-read VC. This covers both initialized immediates
and the indirect fallback used by physical copy. -/
theorem rawRead_resultPre_iff [DecidableEq K] (config : Config)
    (operand : OpTy Provenance) (mplace : MemPlace Provenance)
    (post : ImmediateOrPlace Provenance → State → Prop) (onError : StepError → State → Prop)
    (before : State)
    (checked : CheckedPlaceAccess config false before.machine.memory ⟨before.machine, none⟩
      ⟨mplace, localMemoryLayout operand.layout⟩)
    (indirect : operand.op = .indirect mplace)
    (sized : (localMemoryLayout operand.layout).backendRepr.isUnsized = false) :
    resultPre config before
      (readImmediateRaw before.machine.memory ⟨before.machine, none⟩ operand.op
        (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
        config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout) post onError ↔
    checked.pre (fun selected => resultPre config before
      (finishRawOperandRead ⟨mplace, localMemoryLayout operand.layout⟩
        (readImmediateAfterAccess (localMemoryLayout operand.layout) config.runtime selected))
      post onError) := by
  rw [indirect, rawRead_eq_afterAccess _ _ ⟨mplace, localMemoryLayout operand.layout⟩
    _ _ _ _ _ _ sized]
  simpa only [Bool.false_eq_true, ↓reduceIte] using checked.pre_iff sized
    (fun selected => resultPre config before
      (finishRawOperandRead ⟨mplace, localMemoryLayout operand.layout⟩
        (readImmediateAfterAccess (localMemoryLayout operand.layout) config.runtime selected))
      post onError)

/-- Refine a primitive read VC to its checked memory access, followed by
the interpreter's scalar or scalar-pair ABI and initialization checks. -/
theorem immediateRead_resultPre_iff [DecidableEq K] (config : Config)
    (operand : OpTy Provenance) (mplace : MemPlace Provenance)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) (before : State)
    (checked : CheckedPlaceAccess config false before.machine.memory ⟨before.machine, none⟩
      ⟨mplace, localMemoryLayout operand.layout⟩)
    (indirect : operand.op = .indirect mplace)
    (sized : (localMemoryLayout operand.layout).backendRepr.isUnsized = false)
    (readable : isPrimitiveReadable (localMemoryLayout operand.layout).backendRepr = true) :
    resultPre config before
      (Miri.Interpreter.readImmediate before.machine.memory ⟨before.machine, none⟩ operand.op
        (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
        config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout)
        (fun value => post ⟨value.value, operand.layout⟩) onError ↔
    checked.pre (fun selected =>
      resultPre config before
        (finishImmediateRead (finishRawOperandRead ⟨mplace, localMemoryLayout operand.layout⟩
          (readImmediateAfterAccess (localMemoryLayout operand.layout) config.runtime selected)))
        (fun value => post ⟨value.value, operand.layout⟩) onError) := by
  rw [indirect, immediateRead_eq_afterAccess _ _ ⟨mplace, localMemoryLayout operand.layout⟩
    _ _ _ _ _ _ sized readable]
  simpa only [Bool.false_eq_true, ↓reduceIte] using checked.pre_iff sized
    (fun selected => resultPre config before
      (finishImmediateRead (finishRawOperandRead ⟨mplace, localMemoryLayout operand.layout⟩
        (readImmediateAfterAccess (localMemoryLayout operand.layout) config.runtime selected)))
      (fun value => post ⟨value.value, operand.layout⟩) onError)

/-- Specialized continuation for a single initialized ABI scalar. -/
theorem scalarRead_resultPre_iff [DecidableEq K] (config : Config) (operand : OpTy Provenance)
    (mplace : MemPlace Provenance) (primitive : BackendPrimitive) (validRange : WrappingRange)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) (before : State)
    (checked : CheckedPlaceAccess config false before.machine.memory ⟨before.machine, none⟩
      ⟨mplace, localMemoryLayout operand.layout⟩)
    (indirect : operand.op = .indirect mplace)
    (backend : (localMemoryLayout operand.layout).backendRepr =
      .Scalar (.Initialized (value := primitive) (validRange := validRange)))
    (width : primitive.size config.runtime = .ok (localMemoryLayout operand.layout).size) :
    resultPre config before
      (Miri.Interpreter.readImmediate before.machine.memory ⟨before.machine, none⟩ operand.op
        (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
        config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout)
        (fun value => post ⟨value.value, operand.layout⟩) onError ↔
    checked.pre (fun selected =>
      resultPre config before
        (scalarReadAfterAccess (localMemoryLayout operand.layout) primitive config.runtime selected)
        (fun value => post ⟨value.value, operand.layout⟩) onError) := by
  rw [indirect, scalarRead_eq_afterAccess _ _ ⟨mplace, localMemoryLayout operand.layout⟩
    _ _ _ _ _ _ primitive validRange backend width]
  have sized : (localMemoryLayout operand.layout).backendRepr.isUnsized = false := by
    rw [backend]
    rfl
  simpa only [Bool.false_eq_true, ↓reduceIte] using checked.pre_iff sized
    (fun selected => resultPre config before
      (scalarReadAfterAccess (localMemoryLayout operand.layout) primitive config.runtime selected)
      (fun value => post ⟨value.value, operand.layout⟩) onError)

/-- The dedicated full-place uninit write for a sized place uses the same
checked access, without treating it as an immediate assignment. -/
theorem writeUninit_resultPre_iff [DecidableEq K] (config : Config) (place : MPlaceTy Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) (before : State)
    (checked : CheckedPlaceAccess config true before.machine.memory ⟨before.machine, none⟩
      ⟨place.mplace, localMemoryLayout place.layout⟩)
    (sized : (localMemoryLayout place.layout).backendRepr.isUnsized = false) :
    resultPre config before
      (writeUninitToMplace before.machine.memory ⟨before.machine, none⟩
        ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
        config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout) post onError ↔
    checked.pre (fun selected =>
      resultPre config before (uninitWriteAfterAccess config.runtime.pointerSize selected) post onError) := by
  simpa only [writeUninitToMplace, ↓reduceIte, Id.run, pure, Pure.pure] using checked.pre_iff sized
    (fun selected => resultPre config before (uninitWriteAfterAccess config.runtime.pointerSize selected) post onError)

/-- A full-place uninit write uses the actual extent selected by dynamic
layout. The subsequent pointer access uses its updated memory and hooks. -/
theorem writeUninit_dynamic_resultPre_iff [DecidableEq K] (config : Config) (place : MPlaceTy Provenance)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) (before : State)
    (afterMemory : Memory) (afterHooks : HookState) (size : Size) (align : Align)
    (resolved : config.dynamicLayout before.machine.memory ⟨before.machine, none⟩
      ⟨place.mplace, localMemoryLayout place.layout⟩ = ⟨afterMemory, afterHooks, .ok (some (size, align))⟩)
    (checked : CheckedPlaceAccess config true afterMemory afterHooks
      ⟨place.mplace, {(localMemoryLayout place.layout) with size, align}⟩)
    (unsized : (localMemoryLayout place.layout).backendRepr.isUnsized = true) :
    resultPre config before
      (writeUninitToMplace before.machine.memory ⟨before.machine, none⟩
        ⟨place.mplace, localMemoryLayout place.layout⟩ config.runtime config.ghostMode config.globalKind
        config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout) post onError ↔
    checked.pre (fun selected =>
      resultPre config before (uninitWriteAfterAccess config.runtime.pointerSize selected) post onError) := by
  simp only [writeUninitToMplace, Id.run, pure, Pure.pure]
  rw [unsizedPlaceAccessMut _ _ _ _ ⟨place.mplace, localMemoryLayout place.layout⟩
    _ checked.pointerSize size align _ _ _ _ _ unsized resolved checked.runtimePointerSize]
  simpa only [↓reduceIte] using checked.pre_iff_pointer
    (fun selected => resultPre config before (uninitWriteAfterAccess config.runtime.pointerSize selected) post onError)

/-- Route the production mutable-place callback to the registered typed
memory-write specification. -/
@[spec high] theorem placeHooks_writeMemory [DecidableEq K] {C : Type}
    (config : Config) (allocation : PlaceMachine.AllocationConfig K U)
    (compiler : PlaceMachine.CompilerHooks K U C) (choice : C)
    (value : Immediate Provenance) (place : MPlaceTy Provenance) :
    (PlaceMachine.placeHooks config allocation compiler).writeMemoryNoValidate choice value place =
      PlaceMachine.writeMemory config compiler.willValidateMemory value place := rfl

/-- Route the production optimized-local write callback through its frame,
race and ABI continuations. -/
@[spec high] theorem placeHooks_writeLocal [DecidableEq K] {C : Type}
    (config : Config) (allocation : PlaceMachine.AllocationConfig K U)
    (compiler : PlaceMachine.CompilerHooks K U C) (choice : C) (id : Miri.MIR.LocalId)
    (layout : LocalLayout) (value : Immediate Provenance) :
    (PlaceMachine.placeHooks config allocation compiler).writeLocalImmediate choice id layout value =
      placeWriteLocalImmediate MachineHooks.currentFrame MachineHooks.setCurrentFrame
        compiler.validationInProgress MachineHooks.afterLocalWrite compiler.debugAbiCheck id layout value := rfl

/-- A checked immediate local does not acquire an allocation. The frame is
updated first, then the local race hook and ABI checker see the new state. -/
theorem localImmediateWrite_iff {P S E : Type}
    (getFrame : PlaceM S (Frame P LocalLayout E))
    (setFrame : Frame P LocalLayout E → PlaceM S Unit)
    (validationInProgress : PlaceM S Bool)
    (afterLocalWrite : Miri.MIR.LocalId → Bool → PlaceM S Unit)
    (debugAbiCheck : Immediate P → LocalLayout → PlaceM S Unit)
    (id : Miri.MIR.LocalId) (layout : LocalLayout) (old value : Immediate P)
    (post : Unit → S → Prop) (onError : StepError → S → Prop)
    (before current : S) (frame updated : Frame P LocalLayout E)
    (sized : layout.layout.isSized = true)
    (loaded : getFrame before = .ok frame current)
    (localValue : frame.getLocalOperand id = .ok (.immediate old))
    (written : frame.setLocalOperand id (.immediate value) = .ok updated) :
    wp (placeWriteLocalImmediate getFrame setFrame validationInProgress afterLocalWrite debugAbiCheck
        id layout value) post onError before ↔
      wp (do
        setFrame updated
        unless ← validationInProgress do afterLocalWrite id false
        debugAbiCheck value layout) post onError current := by
  simp only [placeWriteLocalImmediate, sized, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    localValue, written, stackLift_ok, wp, WP.wpTrans, bind, Bind.bind, EStateM.bind,
    loaded, pure, Pure.pure, EStateM.pure]

/-- The raw operand dispatcher checks either an immediate or an indirect
place. Unsized indirect operands bypass bytes and remain places. -/
def rawOperandPre [DecidableEq K] (config : Config) (operand : OpTy Provenance) (before : State)
    (post : Result (ImmediateOrPlace Provenance) → Prop) : Prop :=
  let layout := localMemoryLayout operand.layout
  let hooks : HookState := ⟨before.machine, none⟩
  match operand.op with
  | .immediate value => post ⟨before.machine.memory, hooks, none, .ok (.immediate ⟨value, layout⟩)⟩
  | .indirect mplace =>
    let place : MemoryOperandPlace Provenance := ⟨mplace, layout⟩
    if layout.backendRepr.isUnsized then
      post ⟨before.machine.memory, hooks, none, .ok (.place place)⟩
    else
      placeAccessPre config false before.machine.memory hooks place fun accessed =>
        post (finishRawOperandRead place (readImmediateAfterAccess layout config.runtime accessed))

theorem rawOperandPre_iff [DecidableEq K] (config : Config) (operand : OpTy Provenance)
    (before : State) (post : Result (ImmediateOrPlace Provenance) → Prop) :
    rawOperandPre config operand before post ↔ post
      (readImmediateRaw before.machine.memory ⟨before.machine, none⟩ operand.op
        (localMemoryLayout operand.layout) config.runtime config.ghostMode config.globalKind
        config.globalHooks (PlaceMachine.accessHooks config) config.dynamicLayout) := by
  unfold rawOperandPre
  cases op : operand.op with
  | immediate value => rfl
  | indirect mplace =>
    by_cases unsized : (localMemoryLayout operand.layout).backendRepr.isUnsized = true
    · simp [unsized, readImmediateRaw, readImmediateFromMplaceRaw, finishRawOperandRead]
    · simp only [unsized, readImmediateRaw, readImmediateFromMplaceRaw, Id.run, pure, Pure.pure]
      exact placeAccessPre_iff config false before.machine.memory ⟨before.machine, none⟩
        ⟨mplace, localMemoryLayout operand.layout⟩ (fun accessed =>
          post (finishRawOperandRead ⟨mplace, localMemoryLayout operand.layout⟩
            (readImmediateAfterAccess (localMemoryLayout operand.layout) config.runtime accessed)))

/-- A primitive read's checked value is derived from the raw operand
continuation. Invalid ABI and initialization failures retain the proper state. -/
def immediateReadPre [DecidableEq K] (config : Config) (operand : OpTy Provenance) (before : State)
    (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) : Prop :=
  let finish := fun result => resultPre config before result
    (fun value => post ⟨value.value, operand.layout⟩) onError
  if isPrimitiveReadable (localMemoryLayout operand.layout).backendRepr then
    rawOperandPre config operand before fun loaded => finish (finishImmediateRead loaded)
  else
    finish ⟨before.machine.memory, ⟨before.machine, none⟩, none, .error .invalidPrimitiveRead⟩

theorem immediateReadPre_iff [DecidableEq K] (config : Config) (operand : OpTy Provenance)
    (before : State) (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    immediateReadPre config operand before post onError ↔
      wp (PlaceMachine.readImmediate config operand) post onError before := by
  rw [readImmediate_iff]
  unfold immediateReadPre Miri.Interpreter.readImmediate
  dsimp only
  cases isPrimitiveReadable (localMemoryLayout operand.layout).backendRepr
  · rfl
  · exact rawOperandPre_iff config operand before (fun loaded =>
      resultPre config before (finishImmediateRead loaded) (fun value => post ⟨value.value, operand.layout⟩) onError)

/-- The immediate writer checks sizing and ABI, then pulls back its byte
mutation through the actual place and allocation operations. -/
def immediateWritePre [DecidableEq K] (config : Config)
    (later : MemoryOperandLayout → Bool) (value : Immediate Provenance) (place : MPlaceTy Provenance)
    (before : State) (post : Unit → State → Prop) (onError : StepError → State → Prop) : Prop :=
  let layout := localMemoryLayout place.layout
  let hooks : HookState := ⟨before.machine, none⟩
  let finish := fun result => resultPre config before result post onError
  if layout.backendRepr.isUnsized then
    finish ⟨before.machine.memory, hooks, none, .error .unsizedImmediateWrite⟩
  else
    match immediateMatchesAbi value layout config.runtime with
    | .error error => finish ⟨before.machine.memory, hooks, none, .error error⟩
    | .ok () =>
      placeAccessPre config true before.machine.memory hooks ⟨place.mplace, layout⟩ fun accessed =>
        finish (writeImmediateAfterAccess value layout config.runtime later accessed)

theorem immediateWritePre_iff [DecidableEq K] (config : Config)
    (later : MemoryOperandLayout → Bool) (value : Immediate Provenance) (place : MPlaceTy Provenance)
    (before : State) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    immediateWritePre config later value place before post onError ↔
      wp (PlaceMachine.writeMemory config later value place) post onError before := by
  rw [writeMemory_iff]
  unfold immediateWritePre writeImmediateToMplaceNoValidate
  dsimp only
  cases (localMemoryLayout place.layout).backendRepr.isUnsized
  · cases immediateMatchesAbi value (localMemoryLayout place.layout) config.runtime with
    | error error => rfl
    | ok value' =>
      cases value'
      exact placeAccessPre_iff config true before.machine.memory ⟨before.machine, none⟩
        ⟨place.mplace, localMemoryLayout place.layout⟩ fun accessed =>
          resultPre config before
            (writeImmediateAfterAccess value (localMemoryLayout place.layout) config.runtime later accessed)
            post onError
  · rfl

/-- Full-range uninitialization also accepts a dynamic place. -/
def uninitWritePre [DecidableEq K] (config : Config) (place : MPlaceTy Provenance) (before : State)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) : Prop :=
  placeAccessPre config true before.machine.memory ⟨before.machine, none⟩
    ⟨place.mplace, localMemoryLayout place.layout⟩ fun accessed =>
      resultPre config before (uninitWriteAfterAccess config.runtime.pointerSize accessed) post onError

theorem uninitWritePre_iff [DecidableEq K] (config : Config) (place : MPlaceTy Provenance) (before : State)
    (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    uninitWritePre config place before post onError ↔
      wp (PlaceMachine.writeUninitMemory config place) post onError before := by
  rw [writeUninitMemory_iff]
  exact placeAccessPre_iff config true before.machine.memory ⟨before.machine, none⟩
    ⟨place.mplace, localMemoryLayout place.layout⟩ fun accessed =>
      resultPre config before (uninitWriteAfterAccess config.runtime.pointerSize accessed) post onError

@[spec high] theorem spec_readRaw_symbolic [DecidableEq K] (config : Config) (operand : OpTy Provenance)
    (post : ImmediateOrPlace Provenance → State → Prop) (onError : StepError → State → Prop) :
    Triple (PlaceMachine.readRaw config operand)
      (fun before => rawOperandPre config operand before (fun result => resultPre config before result post onError))
      post onError := by
  apply Triple.iff.mpr
  intro before
  change rawOperandPre config operand before (fun result => resultPre config before result post onError) →
    wp (PlaceMachine.readRaw config operand) post onError before
  rw [readRaw_iff, rawOperandPre_iff]
  exact id

@[spec high] theorem spec_readImmediate_symbolic [DecidableEq K] (config : Config)
    (operand : OpTy Provenance) (post : RvalueImmTy Provenance → State → Prop) (onError : StepError → State → Prop) :
    Triple (PlaceMachine.readImmediate config operand)
      (fun before => immediateReadPre config operand before post onError) post onError :=
  Triple.iff.mpr (fun before => (immediateReadPre_iff config operand before post onError).mp)

@[spec high] theorem spec_writeMemory_symbolic [DecidableEq K] (config : Config)
    (later : MemoryOperandLayout → Bool) (value : Immediate Provenance)
    (place : MPlaceTy Provenance) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (PlaceMachine.writeMemory config later value place)
      (fun before => immediateWritePre config later value place before post onError) post onError :=
  Triple.iff.mpr (fun before => (immediateWritePre_iff config later value place before post onError).mp)

@[spec high] theorem spec_writeUninitMemory_symbolic [DecidableEq K] (config : Config)
    (place : MPlaceTy Provenance) (post : Unit → State → Prop) (onError : StepError → State → Prop) :
    Triple (PlaceMachine.writeUninitMemory config place)
      (fun before => uninitWritePre config place before post onError) post onError :=
  Triple.iff.mpr (fun before => (uninitWritePre_iff config place before post onError).mp)

end Miri.Verification.MemoryWP
