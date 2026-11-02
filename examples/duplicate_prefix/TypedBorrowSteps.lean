import duplicate_prefix.TypedRetagFields
import duplicate_prefix.Storage

/-! Exact composition of the stateful retag source over an existing borrow tree. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.TypedBorrowSteps
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedRetagEntry
open Lean Elab

private def sourceName (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected exact typed source helper {suffix}"
elab "typed_checked" : term => do
  Lean.Meta.mkConstWithFreshMVarLevels (← sourceName ".TypedRetag.checked")
elab "typed_access_error" : term => do
  Lean.Meta.mkConstWithFreshMVarLevels (← sourceName ".TypedRetag.accessError")

/-- This is the unchanged suffix of TypedRetag.reborrow, factored only to
share its kernel proof between protected and unprotected policies. -/
private def readInsert [DecidableEq K] (h : TypedRetag.Hooks K U)
    (location : RetagPipeline.ResolvedLocation) (inside : DedupRangeMap Tree.LocationState)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) : MachineHooks.M K U (Option Provenance) := do
  for segment in inside.iterAll do
    if let some access := segment.data.permission.associatedAccess then
      if access == .Write then
        let some entry := (← get).machine.memory.live.find? (fun entry => entry.1 == location.allocId)
          | throw (.invalidProgram "missing live allocation mutability")
        if entry.2.allocation.mutability == .Not then
          throw .retagWriteToReadOnly
      let offset ← typed_checked "reborrow offset"
        (Size.add location.baseOffset (Size.ofBytes segment.range.start))
      let length := Size.ofBytes (segment.range.stop - segment.range.start)
      let tree ← typed_get_tree location.allocId
      let accessResult := tree.performBorrowAccessRange location.parentProvenance offset length access
        (← typed_tracker (K := K) (User := U)).global.protectedTags .VisitChildrenOfAccessed
      typed_update_tree location.allocId accessResult.tree
      if accessResult.status != .Completed then throw (typed_access_error accessResult.status)
      if length.bytes != 0 then
        match access with
        | .Read => MachineHooks.memoryRaceRead location.allocId (allocRange offset length) .Retag
        | .Write => MachineHooks.memoryRaceWrite location.allocId (allocRange offset length) .Retag
  let tree ← typed_get_tree location.allocId
  let child := tree.newChild location.baseOffset location.parentProvenance tag inside
    policy.outsidePermission policy.protector.isSome
  typed_update_tree location.allocId child.tree
  typed_checked "reborrow child insertion" child.outcome
  return some (Provenance.concrete location.allocId tag)

private theorem tracker_present {K U : Type} (state : MachineHooks.State K U)
    (tracker : MachineHooks.BorrowState) (enabled : state.machine.borrowTracker = some tracker) :
    typed_tracker state = .ok tracker state := by
  unfold_typed ".TypedRetag.tracker"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, enabled]

private theorem read_insert_steps {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (offset len : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (associated : initial.permission.associatedAccess = some .Read)
    (positive : (0 : UInt64) < len)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none) (parentTree finalTree : BorrowTree)
    (readTree : (entry.allocation.extra.performBorrowAccessRange parent (Size.ofBytes offset)
      (Size.ofBytes len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (entry.allocation.extra.performBorrowAccessRange parent (Size.ofBytes offset)
      (Size.ofBytes len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new (Size.ofBytes len) initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩) :
    readInsert h ⟨id, Size.ofBytes offset, parent⟩ (DedupRangeMap.new (Size.ofBytes len) initial)
      policy tag (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames frame
          {machine with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  let start := Storage.withCurrent frames frame machine
  have nonzero : len ≠ 0 := by intro eq; subst len; exact (UInt64.lt_irrefl 0) positive
  unfold readInsert
  simp only [DedupRangeMap.new, DedupRangeMap.iterAll, Size.ofBytes, beq_iff_eq,
    nonzero, ↓reduceIte, ← Array.forIn_toList]
  simp only [List.forIn_cons, List.forIn_nil, associated, bind, EStateM.bind, pure, EStateM.pure]
  unfold_typed ".TypedRetag.checked"
  simp only [beq_iff_eq, reduceCtorEq, Bool.false_eq_true, ↓reduceIte, Size.add,
    Size.ofBytes, UInt64.add_zero, UInt64.lt_irrefl, UInt64.sub_zero,
    bind, EStateM.bind, pure, EStateM.pure]
  have tree := get_tree_present start id entry present
  erw [tree]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  have tracked := tracker_present start tracker enabled
  erw [tracked]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  erw [readTree, readDone]
  have stored := update_tree_present start id entry parentTree present
  erw [stored]
  have completedSelf : (BorrowTree.BorrowTreeAccessStatus.Completed != .Completed) = false := rfl
  simp only [completedSelf, Bool.false_eq_true, ↓reduceIte, bne_iff_ne,
    ite_eq_left nonzero, bind, EStateM.bind, pure, EStateM.pure]
  let parentState := Storage.withCurrent frames frame
    {machine with memory := RetagEntry.updatedMemory machine.memory id entry parentTree}
  have raceRead := race_read_without_clocks parentState id (allocRange (Size.ofBytes offset) (Size.ofBytes len)) race
  erw [raceRead]
  simp only [bind, EStateM.bind, pure, EStateM.pure, List.forIn_nil]
  have parentPresent : parentState.machine.memory.live.find? (fun row => row.1 == id) =
      some (id, {entry with allocation := entry.allocation.setExtra parentTree}) :=
    MemoryCopyBridge.live_lookup_replaced machine.memory id _
  have getParent := get_tree_present parentState id
    {entry with allocation := entry.allocation.setExtra parentTree} parentPresent
  erw [getParent]
  simp only [bind, EStateM.bind, pure, EStateM.pure, Allocation.setExtra, Allocation.mapExtra]
  simp only [DedupRangeMap.new, Size.ofBytes, beq_iff_eq, nonzero, ↓reduceIte] at child
  erw [child]
  have childStored := update_tree_present parentState id
    {entry with allocation := entry.allocation.setExtra parentTree} finalTree parentPresent
  erw [childStored]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  simp only [parentState, start, Storage.withCurrent, RetagEntry.updated_memory_twice]

private theorem zero_insert_steps {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (state : MachineHooks.State K U)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (offset : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission) (finalTree : BorrowTree)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (child : entry.allocation.extra.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new Size.ZERO initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩) :
    readInsert h ⟨id, Size.ofBytes offset, parent⟩ (DedupRangeMap.new Size.ZERO initial) policy tag state =
      .ok (some (.concrete id tag))
        {state with machine := {state.machine with memory :=
          (RetagEntry.updatedMemory state.machine.memory id entry finalTree)}} := by
  unfold readInsert
  simp only [Size.ZERO, Size.ofBytes, DedupRangeMap.new, DedupRangeMap.iterAll,
    beq_iff_eq, ↓reduceIte, ← Array.forIn_toList, List.forIn_nil,
    bind, EStateM.bind, pure, EStateM.pure]
  erw [get_tree_present state id entry present]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  have empty : DedupRangeMap.new Size.ZERO initial = {} := rfl
  rw [empty] at child
  erw [child]
  erw [update_tree_present state id entry finalTree present]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rfl

def registeredGlobal (tracker : MachineHooks.BorrowState) (tag : BorTag) : GlobalState :=
  {tracker.global with protectedTags := tracker.global.protectedTags.insert tag .StrongProtector}

def registeredTracker (tracker : MachineHooks.BorrowState) (tag : BorTag) : MachineHooks.BorrowState :=
  {tracker with global := registeredGlobal tracker tag}

def registeredFrame (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (borrowFrame : FrameState) (id : AllocId) (tag : BorTag) :=
  frameWithBorrow frame (borrowFrame.addProtector id tag)

def registeredMachine {K U : Type} (machine : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) (tag : BorTag) : MachineHooks.MachineState K U :=
  {machine with borrowTracker := some (registeredTracker tracker tag)}

def registeredState {K U : Type}
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (id : AllocId) (tag : BorTag) : MachineHooks.State K U :=
  Storage.withCurrent frames (registeredFrame frame borrowFrame id tag) (registeredMachine machine tracker tag)

/-- Exact source composition. Concrete call summaries must discharge both
borrow-tree equations with the actual Tree Borrows implementation. -/
theorem protected_reborrow_of_steps {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (offset len : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = some .StrongProtector)
    (associated : initial.permission.associatedAccess = some .Read)
    (positive : (0 : UInt64) < len)
    (check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len) (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine))
    (resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame machine) =
      .ok (some ⟨id, Size.ofBytes offset, parent⟩) (Storage.withCurrent frames frame machine))
    (log : h.logCreation place (Size.ofBytes len) policy tag (some ⟨id, Size.ofBytes offset, parent⟩) = pure ())
    (inside : typed_inside h budget place (Size.ofBytes len) policy =
      pure (DedupRangeMap.new (Size.ofBytes len) initial))
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (extraWiring : h.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none) (parentTree finalTree : BorrowTree)
    (readTree : (entry.allocation.extra.performBorrowAccessRange parent (Size.ofBytes offset)
      (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (entry.allocation.extra.performBorrowAccessRange parent (Size.ofBytes offset)
      (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new (Size.ofBytes len) initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩) :
    TypedRetag.reborrow h budget place (Size.ofBytes len) policy tag (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          {registeredMachine machine tracker tag with memory :=
            (RetagEntry.updatedMemory machine.memory id entry finalTree)}) := by
  let start := Storage.withCurrent frames frame machine
  unfold TypedRetag.reborrow
  simp only [check, resolve, log, bind, EStateM.bind, pure, EStateM.pure]
  rw [protection]
  simp only [bind, EStateM.bind]
  rw [current_frame_pushed start frames frame rfl]
  simp only [frameBorrow, bind, EStateM.bind, pure, EStateM.pure]
  erw [tracker_present start tracker enabled]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  simp only [GlobalState.addProtector, FrameState.addProtector, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, MachineHooks.setCurrentFrame,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure,
    set, EStateM.set, start, Storage.withCurrent, Array.isEmpty_push, Array.pop_push,
    Bool.false_eq_true, ↓reduceIte]
  have info := MemoryCopyBridge.live_alloc_info machine.memory id entry present
  unfold_typed ".TypedRetag.checked"
  simp only [info, bind, EStateM.bind, pure, EStateM.pure]
  have liveDataSelf : (AllocationKind.liveData != .liveData) = false := rfl
  simp only [liveDataSelf, Bool.false_eq_true, ↓reduceIte]
  erw [inside]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [extraWiring]
  have ensure := RetagPointerChecks.ensure_tree_live globalKind globals synchronize
    (registeredState frames frame borrowFrame machine tracker id tag) id entry present
  erw [ensure]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  let selectedPolicy := {policy with protector := some .StrongProtector}
  change readInsert h ⟨id, Size.ofBytes offset, parent⟩
    (DedupRangeMap.new (Size.ofBytes len) initial) selectedPolicy tag
    (registeredState frames frame borrowFrame machine tracker id tag) = _
  have selectedChild : parentTree.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new (Size.ofBytes len) initial) selectedPolicy.outsidePermission selectedPolicy.protector.isSome =
      ⟨finalTree, .ok ()⟩ := by simpa only [selectedPolicy, protection] using child
  exact read_insert_steps h frames (registeredFrame frame borrowFrame id tag)
    (registeredMachine machine tracker tag) (registeredTracker tracker tag) rfl id entry offset len parent tag
    initial selectedPolicy associated positive present race parentTree finalTree readTree readDone selectedChild

theorem protected_live_zero_of_steps {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (offset : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = some .StrongProtector)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine))
    (resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame machine) =
      .ok (some ⟨id, Size.ofBytes offset, parent⟩) (Storage.withCurrent frames frame machine))
    (log : h.logCreation place Size.ZERO policy tag (some ⟨id, Size.ofBytes offset, parent⟩) = pure ())
    (inside : typed_inside h budget place Size.ZERO policy =
      pure (DedupRangeMap.new Size.ZERO initial))
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (extraWiring : h.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (finalTree : BorrowTree)
    (child : entry.allocation.extra.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new Size.ZERO initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩) :
    TypedRetag.reborrow h budget place Size.ZERO policy tag (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          {registeredMachine machine tracker tag with memory :=
            (RetagEntry.updatedMemory machine.memory id entry finalTree)}) := by
  let start := Storage.withCurrent frames frame machine
  unfold TypedRetag.reborrow
  simp only [check, resolve, log, bind, EStateM.bind, pure, EStateM.pure]
  rw [protection]
  simp only [bind, EStateM.bind]
  rw [current_frame_pushed start frames frame rfl]
  simp only [frameBorrow, bind, EStateM.bind, pure, EStateM.pure]
  erw [tracker_present start tracker enabled]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  simp only [GlobalState.addProtector, FrameState.addProtector, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, MachineHooks.setCurrentFrame,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure,
    set, EStateM.set, start, Storage.withCurrent, Array.isEmpty_push, Array.pop_push,
    Bool.false_eq_true, ↓reduceIte]
  have info := MemoryCopyBridge.live_alloc_info machine.memory id entry present
  unfold_typed ".TypedRetag.checked"
  simp only [info, bind, EStateM.bind, pure, EStateM.pure]
  have liveDataSelf : (AllocationKind.liveData != .liveData) = false := rfl
  simp only [liveDataSelf, Bool.false_eq_true, ↓reduceIte]
  erw [inside]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [extraWiring]
  have ensure := RetagPointerChecks.ensure_tree_live globalKind globals synchronize
    (registeredState frames frame borrowFrame machine tracker id tag) id entry present
  erw [ensure]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  let selectedPolicy := {policy with protector := some .StrongProtector}
  change readInsert h ⟨id, Size.ofBytes offset, parent⟩
    (DedupRangeMap.new Size.ZERO initial) selectedPolicy tag
    (registeredState frames frame borrowFrame machine tracker id tag) = _
  have selectedChild : entry.allocation.extra.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new Size.ZERO initial) selectedPolicy.outsidePermission selectedPolicy.protector.isSome =
      ⟨finalTree, .ok ()⟩ := by simpa only [selectedPolicy, protection] using child
  have result := zero_insert_steps h
    (registeredState frames frame borrowFrame machine tracker id tag)
    id entry offset parent tag initial selectedPolicy finalTree present selectedChild
  exact result

theorem unprotected_reborrow_of_steps {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (offset len : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = none)
    (associated : initial.permission.associatedAccess = some .Read)
    (positive : (0 : UInt64) < len)
    (check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len) (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine))
    (resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame machine) =
      .ok (some ⟨id, Size.ofBytes offset, parent⟩) (Storage.withCurrent frames frame machine))
    (log : h.logCreation place (Size.ofBytes len) policy tag (some ⟨id, Size.ofBytes offset, parent⟩) = pure ())
    (inside : typed_inside h budget place (Size.ofBytes len) policy =
      pure (DedupRangeMap.new (Size.ofBytes len) initial))
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (extraWiring : h.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none) (parentTree finalTree : BorrowTree)
    (readTree : (entry.allocation.extra.performBorrowAccessRange parent (Size.ofBytes offset)
      (Size.ofBytes len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (entry.allocation.extra.performBorrowAccessRange parent (Size.ofBytes offset)
      (Size.ofBytes len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new (Size.ofBytes len) initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩) :
    TypedRetag.reborrow h budget place (Size.ofBytes len) policy tag (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames frame
          {machine with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  let start := Storage.withCurrent frames frame machine
  unfold TypedRetag.reborrow
  simp only [check, resolve, log, bind, EStateM.bind, pure, EStateM.pure]
  rw [protection]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  have info := MemoryCopyBridge.live_alloc_info machine.memory id entry present
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, Storage.withCurrent, info]
  have liveDataSelf : (AllocationKind.liveData != .liveData) = false := rfl
  simp only [liveDataSelf, Bool.false_eq_true, ↓reduceIte]
  erw [inside]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [extraWiring]
  have ensure := RetagPointerChecks.ensure_tree_live globalKind globals synchronize start id entry present
  erw [ensure]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  let selectedPolicy := {policy with protector := none}
  change readInsert h ⟨id, Size.ofBytes offset, parent⟩
    (DedupRangeMap.new (Size.ofBytes len) initial) selectedPolicy tag start = _
  have selectedChild : parentTree.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new (Size.ofBytes len) initial) selectedPolicy.outsidePermission selectedPolicy.protector.isSome =
      ⟨finalTree, .ok ()⟩ := by simpa only [selectedPolicy, protection] using child
  exact read_insert_steps h frames frame machine tracker enabled id entry offset len parent tag
    initial selectedPolicy associated positive present race parentTree finalTree readTree readDone selectedChild

theorem unprotected_live_zero_of_steps {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (offset : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = none)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine))
    (resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame machine) =
      .ok (some ⟨id, Size.ofBytes offset, parent⟩) (Storage.withCurrent frames frame machine))
    (log : h.logCreation place Size.ZERO policy tag (some ⟨id, Size.ofBytes offset, parent⟩) = pure ())
    (inside : typed_inside h budget place Size.ZERO policy =
      pure (DedupRangeMap.new Size.ZERO initial))
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (extraWiring : h.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (finalTree : BorrowTree)
    (child : entry.allocation.extra.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new Size.ZERO initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩) :
    TypedRetag.reborrow h budget place Size.ZERO policy tag (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames frame
          {machine with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  let start := Storage.withCurrent frames frame machine
  unfold TypedRetag.reborrow
  simp only [check, resolve, log, bind, EStateM.bind, pure, EStateM.pure]
  rw [protection]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  have info := MemoryCopyBridge.live_alloc_info machine.memory id entry present
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, Storage.withCurrent, info]
  have liveDataSelf : (AllocationKind.liveData != .liveData) = false := rfl
  simp only [liveDataSelf, Bool.false_eq_true, ↓reduceIte]
  erw [inside]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [extraWiring]
  have ensure := RetagPointerChecks.ensure_tree_live globalKind globals synchronize start id entry present
  erw [ensure]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  let selectedPolicy := {policy with protector := none}
  change readInsert h ⟨id, Size.ofBytes offset, parent⟩
    (DedupRangeMap.new Size.ZERO initial) selectedPolicy tag start = _
  have selectedChild : entry.allocation.extra.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new Size.ZERO initial) selectedPolicy.outsidePermission selectedPolicy.protector.isSome =
      ⟨finalTree, .ok ()⟩ := by simpa only [selectedPolicy, protection] using child
  have result := zero_insert_steps h start id entry offset parent tag initial
    {policy with protector := none} finalTree present
    (by simpa only [protection] using child)
  exact result

theorem protected_read_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base offset len : UInt64) (parentTag : BorTag) (tag : BorTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = some .StrongProtector)
    (associated : initial.permission.associatedAccess = some .Read)
    (positive : (0 : UInt64) < len)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base + offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none) (parentTree finalTree : BorrowTree)
    (readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read (registeredGlobal tracker tag).protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes len) initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩) :
    TypedRetag.reborrow h budget place (Size.ofBytes len) policy tag (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          {registeredMachine machine tracker tag with memory :=
            (RetagEntry.updatedMemory machine.memory id entry finalTree)}) := by
  let start := Storage.withCurrent frames frame machine
  have check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len) start = .ok () start := by
    rw [sources.check, pointer]
    exact RetagPointerChecks.check_pointer_access_cached pointers access start id parentTag base offset len
      entry pointerWiring width cached present positive signedFits bounds
  have resolve : h.resolveAllocation place.mplace.ptr start =
      .ok (some ⟨id, Size.ofBytes offset, .concrete parentTag⟩) start := by
    rw [sources.resolve, pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers start id parentTag base offset width cached
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place (Size.ofBytes len) policy initial
    initialState sources.precise frozen
  exact protected_reborrow_of_steps h budget place frames frame borrowFrame machine tracker enabled frameBorrow
    id entry offset len (.concrete parentTag) tag initial policy protection associated positive check resolve
    (by rw [sources.log]) inside globalKind globals (Eq.trans sources.ensure extraWiring) synchronize present
    race parentTree finalTree readTree readDone child

theorem unprotected_read_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (base offset len : UInt64) (parentTag : BorTag) (tag : BorTag)
    (initial : Tree.LocationState) (policy : RetagPolicy.NewPermission)
    (protection : policy.protector = none)
    (associated : initial.permission.associatedAccess = some .Read)
    (positive : (0 : UInt64) < len)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (initialState : RetagPolicy.initialLocationState policy true = .ok initial)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base + offset)))
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id, base⟩)
    (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ entry.allocation.byteSize.bytes.toNat)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}})
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : machine.dataRace = none) (parentTree finalTree : BorrowTree)
    (readTree : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (entry.allocation.extra.performBorrowAccessRange (.concrete parentTag) (Size.ofBytes offset)
      (Size.ofBytes len) .Read tracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild (Size.ofBytes offset) (.concrete parentTag) tag
      (DedupRangeMap.new (Size.ofBytes len) initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩) :
    TypedRetag.reborrow h budget place (Size.ofBytes len) policy tag (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames frame
          {machine with memory := RetagEntry.updatedMemory machine.memory id entry finalTree}) := by
  let start := Storage.withCurrent frames frame machine
  have check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len) start = .ok () start := by
    rw [sources.check, pointer]
    exact RetagPointerChecks.check_pointer_access_cached pointers access start id parentTag base offset len
      entry pointerWiring width cached present positive signedFits bounds
  have resolve : h.resolveAllocation place.mplace.ptr start =
      .ok (some ⟨id, Size.ofBytes offset, .concrete parentTag⟩) start := by
    rw [sources.resolve, pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers start id parentTag base offset width cached
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place (Size.ofBytes len) policy initial
    initialState sources.precise frozen
  exact unprotected_reborrow_of_steps h budget place frames frame machine tracker enabled
    id entry offset len (.concrete parentTag) tag initial policy protection associated positive check resolve
    (by rw [sources.log]) inside globalKind globals (Eq.trans sources.ensure extraWiring) synchronize present
    race parentTree finalTree readTree readDone child

#print axioms protected_read_from_fields
#print axioms unprotected_read_from_fields
#print axioms protected_reborrow_of_steps
#print axioms unprotected_reborrow_of_steps
theorem retag_place_of_reborrow {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (size : Size) (align : Align)
    (before after : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : before.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (original : Provenance)
    (provenance : place.mplace.ptr.provenance = some original)
    (sizing : h.sizeAndAlign place = pure (some (size, align)))
    (reborrow : TypedRetag.reborrow h budget place size policy tracker.global.nextPointerTag
      (TypedRetagEmpty.afterTag before tracker fresh) =
      .ok (some (.concrete id tracker.global.nextPointerTag)) after) :
    TypedRetag.retagPlace h budget place policy before =
      .ok (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) after := by
  unfold TypedRetag.retagPlace
  simp only [sizing, bind, EStateM.bind, pure, EStateM.pure, Option.map_some, Option.getD_some]
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, enabled, TypedRetagEmpty.allocate_tag tracker.global fresh]
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure]
  erw [reborrow]
  simp only [provenance, bind, EStateM.bind, pure, EStateM.pure]
  rfl

theorem retag_place_at_of_reborrow {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (size : Size) (align : Align)
    (before after : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : before.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (original : Provenance)
    (provenance : place.mplace.ptr.provenance = some original)
    (sizing : h.sizeAndAlign place before = .ok (some (size, align)) before)
    (reborrow : TypedRetag.reborrow h budget place size policy tracker.global.nextPointerTag
      (TypedRetagEmpty.afterTag before tracker fresh) =
      .ok (some (.concrete id tracker.global.nextPointerTag)) after) :
    TypedRetag.retagPlace h budget place policy before =
      .ok (TypedRetagGeneric.retaggedPlace place id tracker.global.nextPointerTag) after := by
  unfold TypedRetag.retagPlace
  simp only [bind, EStateM.bind]
  rw [sizing]
  simp only [pure, EStateM.pure, Option.map_some, Option.getD_some]
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, enabled, TypedRetagEmpty.allocate_tag tracker.global fresh]
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure]
  erw [reborrow]
  simp only [provenance, bind, EStateM.bind, pure, EStateM.pure]
  rfl

theorem reference_pointer_of_steps {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (value output : RvalueImmTy Provenance)
    (place changed : MPlaceTy Provenance) (pointee : TyId) (mutability : Miri.MIR.Mutability)
    (mode : RetagPolicy.RetagMode) (policy : RetagPolicy.NewPermission)
    (before after : MachineHooks.State K U)
    (shape : h.typeShape value.layout.ty = pure .reference)
    (pointeeQuery : h.referencePointee value.layout.ty = pure (pointee, mutability))
    (permission : TypedRetag.newPermission h pointee
      (if mutability == .Mut then .Mutable else .Shared) mode before = .ok (some policy) before)
    (construct : h.immPtrToMPlace value = pure place)
    (retag : TypedRetag.retagPlace h budget place policy before = .ok changed after)
    (reconstruct : h.reconstruct value changed = pure output) :
    TypedRetag.retagPtrValue h budget value value.layout.ty mode before = .ok (some output) after := by
  unfold TypedRetag.retagPtrValue
  simp only [shape, pointeeQuery, RetagPipeline.RetagTypeShape.reference,
    RetagPipeline.RetagTypeShape.classify, Bool.false_eq_true, ↓reduceIte,
    bind, EStateM.bind, pure, EStateM.pure, permission, construct, retag, reconstruct]

#print axioms retag_place_of_reborrow
#print axioms reference_pointer_of_steps
/-- Zero-length integer provenance never allocates a tree child or protector. -/
theorem no_provenance_zero_reborrow {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (tag : BorTag) (state : MachineHooks.State K U)
    (noProv : place.mplace.ptr.provenance = none)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO state = .ok () state)
    (resolve : h.resolveAllocation place.mplace.ptr state = .ok none state)
    (log : h.logCreation place Size.ZERO policy tag none = pure ()) :
    TypedRetag.reborrow h budget place Size.ZERO policy tag state = .ok none state := by
  unfold TypedRetag.reborrow
  simp only [check, resolve, log, bind, EStateM.bind, pure, EStateM.pure]
  simp [Size.ZERO, noProv, bind, EStateM.bind, pure, EStateM.pure]

theorem no_provenance_zero_from_fields {K U C F A : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (prepared : CompilerFactAdapters.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (sources : TypedRetagFields.SourceFields h prepared access projection vtable pointers choice)
    (budget : Nat) (place : MPlaceTy Provenance) (policy : RetagPolicy.NewPermission)
    (tag : BorTag) (state : ValidityMachine.State K U)
    (noProv : place.mplace.ptr.provenance = none) :
    TypedRetag.reborrow h budget place Size.ZERO policy tag state = .ok none state := by
  apply no_provenance_zero_reborrow
  · exact noProv
  · rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr state
  · rw [sources.resolve]
    exact RetagPointerChecks.resolve_allocation_none pointers place.mplace.ptr state noProv
  · rw [sources.log]

/-- The real zero-sized no-provenance retag preserves the pointer and consumes one tag. -/
theorem no_provenance_zero_retag_place {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (policy : RetagPolicy.NewPermission) (align : Align)
    (before : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : before.machine.borrowTracker = some tracker)
    (fresh : tracker.global.nextPointerTag.value < 18446744073709551615)
    (noProv : place.mplace.ptr.provenance = none)
    (sizing : h.sizeAndAlign place = pure (some (Size.ZERO, align)))
    (reborrow : TypedRetag.reborrow h budget place Size.ZERO policy tracker.global.nextPointerTag
      (TypedRetagEmpty.afterTag before tracker fresh) =
      .ok none (TypedRetagEmpty.afterTag before tracker fresh)) :
    TypedRetag.retagPlace h budget place policy before =
      .ok place (TypedRetagEmpty.afterTag before tracker fresh) := by
  unfold TypedRetag.retagPlace
  simp only [sizing, bind, EStateM.bind, pure, EStateM.pure, Option.map_some, Option.getD_some]
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, enabled, TypedRetagEmpty.allocate_tag tracker.global fresh]
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure]
  erw [reborrow]
  simp only [noProv, bind, EStateM.bind, pure, EStateM.pure]
  simp only [← noProv]

#print axioms no_provenance_zero_from_fields
#print axioms no_provenance_zero_retag_place

/-- A zero-sized reborrow of a known nonlive allocation registers protection
without reading or constructing a borrow tree. -/
theorem protected_nonlive_zero_of_metadata {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (offset : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (policy : RetagPolicy.NewPermission) (protection : policy.protector = some .StrongProtector)
    (info : Miri.Memory.AllocationInfo)
    (metadata : machine.memory.getAllocInfo id = .ok info)
    (nonlive : info.kind ≠ .liveData)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO (Storage.withCurrent frames frame machine) =
      .ok () (Storage.withCurrent frames frame machine))
    (resolve : h.resolveAllocation place.mplace.ptr (Storage.withCurrent frames frame machine) =
      .ok (some ⟨id, Size.ofBytes offset, parent⟩) (Storage.withCurrent frames frame machine))
    (log : h.logCreation place Size.ZERO policy tag (some ⟨id, Size.ofBytes offset, parent⟩) = pure ()) :
    TypedRetag.reborrow h budget place Size.ZERO policy tag (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag)) (registeredState frames frame borrowFrame machine tracker id tag) := by
  let start := Storage.withCurrent frames frame machine
  unfold TypedRetag.reborrow
  simp only [check, resolve, log, bind, EStateM.bind, pure, EStateM.pure]
  rw [protection]
  simp only [bind, EStateM.bind]
  rw [current_frame_pushed start frames frame rfl]
  simp only [frameBorrow, bind, EStateM.bind, pure, EStateM.pure]
  erw [tracker_present start tracker enabled]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  simp only [GlobalState.addProtector, FrameState.addProtector, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, MachineHooks.setCurrentFrame,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure,
    set, EStateM.set, start, Storage.withCurrent, Array.isEmpty_push, Array.pop_push,
    Bool.false_eq_true, ↓reduceIte]
  unfold_typed ".TypedRetag.checked"
  simp only [metadata, bind, EStateM.bind, pure, EStateM.pure]
  simp [nonlive, Size.ZERO, registeredState, registeredFrame, registeredMachine,
    registeredTracker, registeredGlobal, frameWithBorrow, FrameState.addProtector,
    Storage.withCurrent, bind, EStateM.bind, pure, EStateM.pure]

#print axioms protected_nonlive_zero_of_metadata

end DuplicatePrefix.TypedBorrowSteps

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.TypedBorrowSteps.protected_reborrow_of_steps,
      ``DuplicatePrefix.TypedBorrowSteps.unprotected_reborrow_of_steps,
      ``DuplicatePrefix.TypedBorrowSteps.protected_read_from_fields,
      ``DuplicatePrefix.TypedBorrowSteps.unprotected_read_from_fields,
      ``DuplicatePrefix.TypedBorrowSteps.retag_place_of_reborrow,
      ``DuplicatePrefix.TypedBorrowSteps.reference_pointer_of_steps,
      ``DuplicatePrefix.TypedBorrowSteps.no_provenance_zero_reborrow,
      ``DuplicatePrefix.TypedBorrowSteps.no_provenance_zero_from_fields,
      ``DuplicatePrefix.TypedBorrowSteps.no_provenance_zero_retag_place,
      ``DuplicatePrefix.TypedBorrowSteps.protected_nonlive_zero_of_metadata,
      ``DuplicatePrefix.TypedBorrowSteps.protected_live_zero_of_steps,
      ``DuplicatePrefix.TypedBorrowSteps.unprotected_live_zero_of_steps,
      ``DuplicatePrefix.TypedBorrowSteps.retag_place_at_of_reborrow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
