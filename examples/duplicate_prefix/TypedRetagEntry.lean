import duplicate_prefix.RetagEntry
import duplicate_prefix.RetagPointerChecks
import duplicate_prefix.SliceDynamicLayout
import duplicate_prefix.RetagReferencePlace
import Miri.Input.CompilerRetagOptions

/-! The canonical stateful typed retag driver, using the real pointer leaves. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.TypedRetagEntry
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open Lean Elab Tactic

private def sourceName (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected exact typed source helper {suffix}"

elab "unfold_typed " suffix:str : tactic => do
  let name := mkIdent (← sourceName suffix.getString)
  evalTactic (← `(tactic| unfold $name:ident))

elab "typed_get_tree" : term => return mkConst (← sourceName ".TypedRetag.getTree")
elab "typed_update_tree" : term => return mkConst (← sourceName ".TypedRetag.updateTree")
elab "typed_inside" : term => return mkConst (← sourceName ".TypedRetag.insidePermissions")
elab "typed_tracker" : term => return mkConst (← sourceName ".TypedRetag.tracker")

def allocatedGlobal (id : AllocId) : GlobalState :=
  {RetagEntry.entryGlobal id with nextPointerTag := ⟨3, by decide⟩}

def frameWithBorrow (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (borrowFrame : FrameState) : Frame Provenance LocalLayout MachineHooks.FrameExtra :=
  {frame with extra := {frame.extra with borrowTracker := some borrowFrame}}

def entryState {K U : Type} (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (borrowFrame : FrameState) (id : AllocId) : MachineHooks.State K U :=
  {ambient with
    stack := ⟨frames.push (frameWithBorrow frame borrowFrame)⟩
    machine := {ambient.machine with borrowTracker := some ⟨allocatedGlobal id, .FnEntry⟩}}

def protectedState {K U : Type} (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (borrowFrame : FrameState) (id : AllocId) : MachineHooks.State K U :=
  {ambient with
    stack := ⟨frames.push (frameWithBorrow frame (RetagEntry.protectedFrame borrowFrame id))⟩
    machine := {ambient.machine with borrowTracker := some ⟨RetagEntry.protectedGlobal id, .FnEntry⟩}}

def beforeTagState {K U : Type} (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (borrowFrame : FrameState) (id : AllocId) : MachineHooks.State K U :=
  {entryState ambient frames frame borrowFrame id with machine :=
    {ambient.machine with borrowTracker := some ⟨RetagEntry.entryGlobal id, .FnEntry⟩}}

def completedState {K U : Type} (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity offset len : UInt64) : MachineHooks.State K U :=
  {protectedState ambient frames frame borrowFrame id with machine :=
    {(protectedState ambient frames frame borrowFrame id).machine with
      memory := RetagEntry.updatedMemory ambient.machine.memory id entry
        (RetagEntry.childTree capacity offset len)}}

def retaggedPlace (place : MPlaceTy Provenance) (id : AllocId) : MPlaceTy Provenance :=
  {place with mplace := {place.mplace with ptr :=
    {place.mplace.ptr with provenance := some (.concrete id ChildBorrow.childTag)}}}

theorem current_frame_entry {K U : Type} (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (borrowFrame : FrameState) (id : AllocId) :
    MachineHooks.currentFrame (entryState ambient frames frame borrowFrame id) =
      .ok (frameWithBorrow frame borrowFrame) (entryState ambient frames frame borrowFrame id) := by
  unfold MachineHooks.currentFrame
  simp [entryState, Stack.currentFrame?, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, pure, EStateM.pure]

theorem current_frame_pushed {K U : Type} (state : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (shape : state.stack.frames = frames.push frame) :
    MachineHooks.currentFrame state = .ok frame state := by
  unfold MachineHooks.currentFrame
  simp [Stack.currentFrame?, shape, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, pure, EStateM.pure]

theorem machine_retag_enabled {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (value : RvalueImmTy Provenance) (ty : TyId)
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : state.machine.borrowTracker = some tracker) :
    TypedRetag.machineRetagPtrValue h budget value ty state =
      TypedRetag.retagPtrValue h budget value ty tracker.retagMode state := by
  unfold TypedRetag.machineRetagPtrValue
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, enabled]

theorem get_tree_present {K U : Type}
    (state : MachineHooks.State K U) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry)) :
    typed_get_tree id state = .ok entry.allocation.extra state := by
  unfold_typed ".TypedRetag.getTree"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, present]

theorem update_tree_present {K U : Type} [DecidableEq K]
    (state : MachineHooks.State K U) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (present : state.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry)) :
    typed_update_tree id tree state = .ok ()
      {state with machine := {state.machine with
        memory := RetagEntry.updatedMemory state.machine.memory id entry tree}} := by
  have stored := MemoryCopyBridge.set_live_exact state.machine.memory id entry
    (entry.allocation.setExtra tree) present
  unfold_typed ".TypedRetag.updateTree"
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, present, stored, set, EStateM.set]
  rfl

theorem race_read_without_clocks {K U : Type} (state : MachineHooks.State K U)
    (id : AllocId) (range : AllocRange)
    (disabled : state.machine.dataRace = none) :
    MachineHooks.memoryRaceRead id range .Retag state = .ok () state := by
  have access := MemoryCopyBridge.race_access_without_clocks state.machine id range
    none .Retag disabled
  unfold MachineHooks.memoryRaceRead
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, access, set, EStateM.set]

theorem canonical_inside {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared)
    (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (budget : Nat) (place : MPlaceTy Provenance) (size : Size)
    (frozen : CompilerFacts.boolean prepared.context place.layout.ty "is_freeze" = .ok true) :
    typed_inside (EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice)
      budget place size ChildBorrow.fnEntryPolicy =
      pure (DedupRangeMap.new size ChildBorrow.fnEntryLocation) := by
  unfold_typed ".TypedRetag.insidePermissions"
  unfold_typed ".TypedRetag.checked"
  simp only [EvalRetagMachine.hooks, CompilerRetagOptions.make]
  unfold_typed ".EvalRetagMachine.lift"
  funext state
  simp [frozen, ChildBorrow.mutable_fn_entry_initial_location, bind, EStateM.bind,
    pure, EStateM.pure]

theorem canonical_new_permission {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (pointee : TyId) (state : ValidityMachine.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra)
    (shape : state.stack.frames = frames.push frame)
    (unpin : CompilerFacts.boolean prepared.context pointee "is_unpin" = .ok true)
    (unsafeUnpin : CompilerFacts.boolean prepared.context pointee "is_unsafe_unpin" = .ok true)
    (freeze : CompilerFacts.boolean prepared.context pointee "is_freeze" = .ok true) :
    TypedRetag.newPermission (EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice)
      pointee .Mutable .FnEntry state = .ok (some ChildBorrow.fnEntryPolicy) state := by
  unfold TypedRetag.newPermission
  simp only [EvalRetagMachine.hooks, CompilerRetagOptions.make]
  unfold_typed ".EvalRetagMachine.lift"
  simp only [unpin, unsafeUnpin, freeze, beq_iff_eq, reduceCtorEq, ↓reduceIte,
    bind, EStateM.bind, pure, EStateM.pure, Bool.true_eq]
  rw [current_frame_pushed state frames frame shape]
  have policy : RetagPolicy.create ⟨true, true, true⟩ .Mutable .FnEntry ⟨false, false⟩ =
      some ChildBorrow.fnEntryPolicy := by decide
  simp only [bind, EStateM.bind, pure, EStateM.pure, Bool.false_eq_true, ↓reduceIte, policy]

/-- Immutable type/layout and fat-pointer metadata used by the actual DST
size computation; no retag or memory success appears in this contract. -/
structure SliceFacts {K U C : Type}
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (choice : C) (place : MPlaceTy Provenance) (len : UInt64) where
  element : TyAndLayout TyId
  fuel : Nat
  fuel_eq : projection.dynamicFuel = fuel + 1
  metadata_eq : place.mplace.metadata = .metadata (Scalar.fromScalarInt (ScalarInt.ofUInt64 len))
  unsized : place.layout.layout.isSized = false
  kind : projection.dynamic.classify choice place.layout.ty = pure .slice
  field : projection.dynamic.field choice place.layout 0 = pure element
  elementSize : element.layout.size = Size.ofBytes 1
  elementAlign : element.layout.align.abi = Align.ONE
  width : projection.dynamic.target.pointerWidth = .w64
  bounded : len ≤ projection.dynamic.maxSizeOfVal.bytes

theorem canonical_size {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (place : MPlaceTy Provenance) (len : UInt64) (facts : SliceFacts projection choice place len) :
    (EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice).sizeAndAlign
      place = pure (some (Size.ofBytes len, Align.ONE)) := by
  change DynamicLayout.sizeAndAlignFromMeta (PlaceDynamic.withVTable projection.dynamic vtable)
    choice projection.dynamicFuel place.mplace.metadata place.layout = _
  rw [facts.fuel_eq, facts.metadata_eq]
  exact SliceDynamicLayout.u8_slice_size _ choice facts.fuel place.layout facts.element len
    facts.unsized facts.kind facts.field facts.elementSize facts.elementAlign facts.width facts.bounded

private theorem reborrow_stage {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity offset len : UInt64)
    (check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len)
      (entryState ambient frames frame borrowFrame id) =
      .ok () (entryState ambient frames frame borrowFrame id))
    (resolve : h.resolveAllocation place.mplace.ptr
      (entryState ambient frames frame borrowFrame id) =
      .ok (some ⟨id, Size.ofBytes offset, .concrete ChildBorrow.rootTag⟩)
        (entryState ambient frames frame borrowFrame id))
    (log : h.logCreation place (Size.ofBytes len) ChildBorrow.fnEntryPolicy ChildBorrow.childTag
      (some ⟨id, Size.ofBytes offset, .concrete ChildBorrow.rootTag⟩) = pure ())
    (inside : typed_inside h budget place (Size.ofBytes len) ChildBorrow.fnEntryPolicy =
      pure (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation))
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (extraWiring : h.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view =>
      {view with machine := {view.machine with memory}})
    (present : ambient.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (root : entry.allocation.extra = BorrowTree.new ChildBorrow.rootTag (Size.ofBytes capacity))
    (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (race : ambient.machine.dataRace = none) :
    TypedRetag.reborrow h budget place (Size.ofBytes len) ChildBorrow.fnEntryPolicy
      ChildBorrow.childTag (entryState ambient frames frame borrowFrame id) =
      .ok (some (.concrete id ChildBorrow.childTag))
        {protectedState ambient frames frame borrowFrame id with machine :=
          {(protectedState ambient frames frame borrowFrame id).machine with
            memory := RetagEntry.updatedMemory ambient.machine.memory id entry
              (RetagEntry.childTree capacity offset len)}} := by
  unfold TypedRetag.reborrow
  simp only [bind, EStateM.bind, check, resolve, log, pure, EStateM.pure]
  simp only [ChildBorrow.fnEntryPolicy]
  simp only [bind, EStateM.bind]
  rw [current_frame_entry]
  simp only [frameWithBorrow]
  unfold_typed ".TypedRetag.tracker"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, entryState]
  simp only [allocatedGlobal, RetagEntry.register_child_protector]
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    MachineHooks.setCurrentFrame, get, getThe, MonadStateOf.get, EStateM.get,
    bind, EStateM.bind, pure, EStateM.pure, set, EStateM.set,
    Array.isEmpty_push, Array.pop_push, ↓reduceIte]
  simp only [Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, EStateM.set]
  have info := MemoryCopyBridge.live_alloc_info ambient.machine.memory id entry present
  unfold_typed ".TypedRetag.checked"
  simp only [info, bind, EStateM.bind, pure, EStateM.pure]
  have liveDataSelf : (AllocationKind.liveData != .liveData) = false := rfl
  simp only [liveDataSelf, Bool.false_eq_true, ↓reduceIte]
  erw [inside]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rw [extraWiring]
  have ensure := RetagPointerChecks.ensure_tree_live globalKind globals synchronize
    (protectedState ambient frames frame borrowFrame id) id entry present
  erw [ensure]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  have nonzero : len ≠ 0 := by intro eq; subst len; exact (UInt64.lt_irrefl 0) positive
  simp only [DedupRangeMap.new, DedupRangeMap.iterAll, Size.ofBytes, beq_iff_eq,
    nonzero, ↓reduceIte, ← Array.forIn_toList]
  simp only [List.forIn_cons, List.forIn_nil, ChildBorrow.fnEntryLocation,
    Permission.associatedAccess, bind, EStateM.bind, pure, EStateM.pure]
  simp only [reduceCtorEq, Bool.false_eq_true, ↓reduceIte, Size.add,
    Size.ofBytes, UInt64.add_zero, UInt64.lt_irrefl, UInt64.sub_zero]
  simp only [Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind, pure, EStateM.pure]
  have rootTree := get_tree_present (protectedState ambient frames frame borrowFrame id)
    id entry present
  erw [rootTree]
  simp only [bind, EStateM.bind, pure, EStateM.pure, root]
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, protectedState, RetagEntry.protectedGlobal,
    ProtectedTags.insert, Array.filter_empty, Array.push_empty]
  have distinct : ChildBorrow.rootTag ≠ ChildBorrow.childTag := by decide
  have parentAccess := ParentBorrowAccess.parent_with_child_protector
    ChildBorrow.rootTag ChildBorrow.childTag capacity offset len .Read distinct positive bounds
  simp only [BorrowRangeAccess.childProtected] at parentAccess
  erw [parentAccess.1, parentAccess.2]
  let parentTree := {BorrowTree.new ChildBorrow.rootTag (Size.ofBytes capacity) with
    locations := RangeMapNonempty.intervalPartition capacity offset (offset + len)
      BorrowRangeAccess.rootLocation}
  have parentStored := update_tree_present (protectedState ambient frames frame borrowFrame id)
    id entry parentTree present
  erw [parentStored]
  have completedSelf : (BorrowTree.BorrowTreeAccessStatus.Completed != .Completed) = false := rfl
  simp only [completedSelf, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind,
    pure, EStateM.pure, bne_iff_ne, ite_eq_left nonzero]
  let parentState := {protectedState ambient frames frame borrowFrame id with machine :=
    {(protectedState ambient frames frame borrowFrame id).machine with
      memory := RetagEntry.updatedMemory ambient.machine.memory id entry parentTree}}
  have raceRead := race_read_without_clocks parentState id
    (allocRange (Size.ofBytes offset) (Size.ofBytes len)) race
  erw [raceRead]
  simp only [bind, EStateM.bind, pure, EStateM.pure, List.forIn_nil]
  have parentPresent : parentState.machine.memory.live.find? (fun row => row.1 == id) =
      some (id, {entry with allocation := entry.allocation.setExtra parentTree}) :=
    MemoryCopyBridge.live_lookup_replaced ambient.machine.memory id _
  have getParent := get_tree_present parentState id
    {entry with allocation := entry.allocation.setExtra parentTree} parentPresent
  erw [getParent]
  simp only [bind, EStateM.bind, pure, EStateM.pure, Allocation.setExtra, Allocation.mapExtra]
  have childStep := ChildConstructor.new_child_partition_exact
    ChildBorrow.rootTag ChildBorrow.childTag distinct capacity offset len positive bounds
  simp only [DedupRangeMap.new, Size.ofBytes, beq_iff_eq, nonzero, ↓reduceIte,
    ChildBorrow.fnEntryLocation] at childStep
  erw [childStep]
  have childStored := update_tree_present parentState id
    {entry with allocation := entry.allocation.setExtra parentTree}
    (RetagEntry.childTree capacity offset len) parentPresent
  erw [childStored]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  simp only [parentState, RetagEntry.updated_memory_twice]
  rfl

theorem canonical_reborrow {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (budget : Nat) (place : MPlaceTy Provenance) (ambient : ValidityMachine.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity base offset len : UInt64)
    (pointer : place.mplace.ptr =
      Pointer.new (some (.concrete id ChildBorrow.rootTag)) (Size.ofBytes (base + offset)))
    (frozen : CompilerFacts.boolean prepared.context place.layout.ty "is_freeze" = .ok true)
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view =>
      {view with machine := {view.machine with memory}})
    (cached : ambient.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (present : ambient.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (root : entry.allocation.extra = BorrowTree.new ChildBorrow.rootTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (race : ambient.machine.dataRace = none) :
    let h := EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
    TypedRetag.reborrow h budget place (Size.ofBytes len) ChildBorrow.fnEntryPolicy
      ChildBorrow.childTag (entryState ambient frames frame borrowFrame id) =
      .ok (some (.concrete id ChildBorrow.childTag))
        {protectedState ambient frames frame borrowFrame id with machine :=
          {(protectedState ambient frames frame borrowFrame id).machine with
            memory := RetagEntry.updatedMemory ambient.machine.memory id entry
              (RetagEntry.childTree capacity offset len)}} := by
  let h := EvalRetagMachine.hooks prepared runtime
    (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
  have checked : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len)
      (entryState ambient frames frame borrowFrame id) =
      .ok () (entryState ambient frames frame borrowFrame id) := by
    change ValidityMachine.checkPointerAccess access place.mplace.ptr (Size.ofBytes len) _ = _
    rw [pointer]
    exact RetagPointerChecks.check_pointer_access_cached pointers access
      (entryState ambient frames frame borrowFrame id) id ChildBorrow.rootTag base offset len entry
      pointerWiring width cached present positive signedFits (by simpa only [allocationSize, Size.ofBytes] using bounds)
  have resolved : h.resolveAllocation place.mplace.ptr
      (entryState ambient frames frame borrowFrame id) =
      .ok (some ⟨id, Size.ofBytes offset, .concrete ChildBorrow.rootTag⟩)
        (entryState ambient frames frame borrowFrame id) := by
    change TypedValidityProviders.resolveAllocation pointers place.mplace.ptr _ = _
    rw [pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers
      (entryState ambient frames frame borrowFrame id) id ChildBorrow.rootTag base offset width cached
  exact reborrow_stage h budget place ambient frames frame borrowFrame id entry capacity offset len
    checked resolved (by rfl)
    (canonical_inside prepared runtime compiler access projection vtable pointers choice budget place
      (Size.ofBytes len) frozen) globalKind globals extraWiring synchronize present root positive bounds race

private theorem retag_place_stage {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity offset len : UInt64)
    (size : h.sizeAndAlign place = pure (some (Size.ofBytes len, Align.ONE)))
    (provenance : place.mplace.ptr.provenance = some (.concrete id ChildBorrow.rootTag))
    (reborrow : TypedRetag.reborrow h budget place (Size.ofBytes len) ChildBorrow.fnEntryPolicy
      ChildBorrow.childTag (entryState ambient frames frame borrowFrame id) =
      .ok (some (.concrete id ChildBorrow.childTag))
        (completedState ambient frames frame borrowFrame id entry capacity offset len)) :
    TypedRetag.retagPlace h budget place ChildBorrow.fnEntryPolicy
      (beforeTagState ambient frames frame borrowFrame id) =
      .ok (retaggedPlace place id)
        (completedState ambient frames frame borrowFrame id entry capacity offset len) := by
  unfold TypedRetag.retagPlace
  simp only [size, bind, EStateM.bind, pure, EStateM.pure, Option.map_some, Option.getD_some]
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, beforeTagState, RetagEntry.allocate_child_tag]
  simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet,
    bind, EStateM.bind, pure, EStateM.pure]
  erw [reborrow]
  simp only [provenance, bind, EStateM.bind, pure, EStateM.pure]
  rfl

theorem canonical_retag_place {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (budget : Nat) (place : MPlaceTy Provenance) (ambient : ValidityMachine.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity base offset len : UInt64)
    (pointer : place.mplace.ptr =
      Pointer.new (some (.concrete id ChildBorrow.rootTag)) (Size.ofBytes (base + offset)))
    (frozen : CompilerFacts.boolean prepared.context place.layout.ty "is_freeze" = .ok true)
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view =>
      {view with machine := {view.machine with memory}})
    (cached : ambient.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (present : ambient.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (root : entry.allocation.extra = BorrowTree.new ChildBorrow.rootTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (slice : SliceFacts projection choice place len)
    (race : ambient.machine.dataRace = none) :
    let h := EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
    TypedRetag.retagPlace h budget place ChildBorrow.fnEntryPolicy
      (beforeTagState ambient frames frame borrowFrame id) =
      .ok (retaggedPlace place id)
        (completedState ambient frames frame borrowFrame id entry capacity offset len) := by
  have provenance : place.mplace.ptr.provenance = some (.concrete id ChildBorrow.rootTag) := by
    rw [pointer]
    rfl
  exact retag_place_stage _ budget place ambient frames frame borrowFrame id entry capacity offset len
    (canonical_size prepared runtime compiler access projection vtable pointers choice place len slice)
    provenance
    (canonical_reborrow prepared runtime compiler access projection vtable pointers choice budget place
      ambient frames frame borrowFrame id entry capacity base offset len pointer frozen pointerWiring width
      globalKind globals extraWiring synchronize cached present root allocationSize positive signedFits bounds race)

private theorem retag_pointer_stage {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (value output : RvalueImmTy Provenance)
    (place changed : MPlaceTy Provenance) (pointee : TyId)
    (before after : MachineHooks.State K U)
    (shape : h.typeShape value.layout.ty = pure .reference)
    (pointeeQuery : h.referencePointee value.layout.ty = pure (pointee, .Mut))
    (policy : TypedRetag.newPermission h pointee .Mutable .FnEntry before =
      .ok (some ChildBorrow.fnEntryPolicy) before)
    (construct : h.immPtrToMPlace value = pure place)
    (retag : TypedRetag.retagPlace h budget place ChildBorrow.fnEntryPolicy before =
      .ok changed after)
    (reconstruct : h.reconstruct value changed = pure output) :
    TypedRetag.retagPtrValue h budget value value.layout.ty .FnEntry before =
      .ok (some output) after := by
  unfold TypedRetag.retagPtrValue
  simp only [shape, pointeeQuery, RetagPipeline.RetagTypeShape.reference,
    RetagPipeline.RetagTypeShape.classify, Bool.false_eq_true, ↓reduceIte,
    bind, EStateM.bind, pure, EStateM.pure]
  have mutable : (Miri.MIR.Mutability.Mut == .Mut) = true := rfl
  simp only [mutable, ↓reduceIte, policy, construct, retag, reconstruct,
    bind, EStateM.bind, pure, EStateM.pure]

theorem canonical_retag_pointer {K U C F A : Type} [DecidableEq K]
    (prepared : CompilerFactAdapters.Prepared) (runtime : CompilerRuntimeQueries.Prepared)
    (compiler : CompilerProviders.Prepared) (access : ValidityMachine.Access K U)
    (projection : PlaceProjectionHooks Provenance (ValidityMachine.State K U) C MachineHooks.FrameExtra)
    (vtable : VTableHooks Provenance (ValidityMachine.State K U) C F A)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U)) (choice : C)
    (budget : Nat) (place : MPlaceTy Provenance) (reference : LocalLayout) (ambient : ValidityMachine.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity base offset len : UInt64)
    (pointer : place.mplace.ptr =
      Pointer.new (some (.concrete id ChildBorrow.rootTag)) (Size.ofBytes (base + offset)))
    (frozen : CompilerFacts.boolean prepared.context place.layout.ty "is_freeze" = .ok true)
    (pointerWiring : access.resolvePointer = TypedMemoryProviders.resolvePointer pointers)
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view =>
      {view with machine := {view.machine with memory}})
    (cached : ambient.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) =
      some ⟨id, base⟩)
    (present : ambient.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (root : entry.allocation.extra = BorrowTree.new ChildBorrow.rootTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (slice : SliceFacts projection choice place len)
    (placeShape : place = RetagReferencePlace.slicePlace
      (Pointer.new (.concrete id ChildBorrow.rootTag) (Size.ofBytes (base + offset))) len place.layout)
    (referenceShape : CompilerFacts.retagTypeShape prepared.context reference.ty = .ok .reference)
    (referencePointee : CompilerFacts.referencePointee prepared.context reference.ty =
      .ok (place.layout.ty, .Mut))
    (dereference : CompilerFacts.builtinDeref prepared.context reference.ty true = .ok (some place.layout.ty))
    (pointeeLayout : CompilerFacts.layoutOf prepared.context place.layout.ty = .ok place.layout)
    (pointeeAlign : place.layout.layout.align.abi = Align.ONE)
    (unpin : CompilerFacts.boolean prepared.context place.layout.ty "is_unpin" = .ok true)
    (unsafeUnpin : CompilerFacts.boolean prepared.context place.layout.ty "is_unsafe_unpin" = .ok true)
    (race : ambient.machine.dataRace = none) :
    let h := EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
    TypedRetag.retagPtrValue h budget
      (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id ChildBorrow.rootTag) (Size.ofBytes (base + offset))) len reference)
      reference.ty .FnEntry (beforeTagState ambient frames frame borrowFrame id) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id ChildBorrow.childTag) (Size.ofBytes (base + offset))) len reference))
        (completedState ambient frames frame borrowFrame id entry capacity offset len) := by
  let h := EvalRetagMachine.hooks prepared runtime
    (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
  let oldPointer := Pointer.new (Provenance.concrete id ChildBorrow.rootTag) (Size.ofBytes (base + offset))
  let newPointer := Pointer.new (Provenance.concrete id ChildBorrow.childTag) (Size.ofBytes (base + offset))
  let value := RetagReferencePlace.sliceValue access.runtime.base oldPointer len reference
  let output := RetagReferencePlace.sliceValue access.runtime.base newPointer len reference
  have shape : h.typeShape value.layout.ty = pure .reference := by
    simp only [h, value, RetagReferencePlace.sliceValue, EvalRetagMachine.hooks]
    unfold_typed ".EvalRetagMachine.lift"
    rw [referenceShape]
  have pointee : h.referencePointee value.layout.ty = pure (place.layout.ty, .Mut) := by
    simp only [h, value, RetagReferencePlace.sliceValue, EvalRetagMachine.hooks]
    unfold_typed ".EvalRetagMachine.lift"
    rw [referencePointee]
  have policy := canonical_new_permission prepared runtime compiler access projection vtable pointers choice
    place.layout.ty (beforeTagState ambient frames frame borrowFrame id) frames
    (frameWithBorrow frame borrowFrame) rfl unpin unsafeUnpin frozen
  have construct : h.immPtrToMPlace value = pure place := by
    change PointerPlaceMachine.fromImmediate access (CompilerExecutionProviders.pointerCompiler prepared)
      choice value = pure place
    exact Eq.trans (RetagReferencePlace.canonical_from_immediate access prepared choice oldPointer len
      reference place.layout dereference pointeeLayout pointeeAlign) (congrArg pure placeShape.symm)
  have changed : retaggedPlace place id = RetagReferencePlace.slicePlace newPointer len place.layout := by
    rw [placeShape]
    rfl
  have reconstruct : h.reconstruct value (retaggedPlace place id) = pure output := by
    rw [changed]
    exact RetagReferencePlace.canonical_reconstruct prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
      value newPointer len place.layout
  exact retag_pointer_stage h budget value output place (retaggedPlace place id) place.layout.ty
    (beforeTagState ambient frames frame borrowFrame id)
    (completedState ambient frames frame borrowFrame id entry capacity offset len)
    shape pointee policy construct
    (canonical_retag_place prepared runtime compiler access projection vtable pointers choice budget place
      ambient frames frame borrowFrame id entry capacity base offset len pointer frozen pointerWiring width
      globalKind globals extraWiring synchronize cached present root allocationSize positive signedFits bounds slice race)
    reconstruct

#print axioms canonical_retag_pointer
#print axioms canonical_new_permission
#print axioms canonical_retag_place
#print axioms canonical_size
#print axioms canonical_reborrow
#print axioms get_tree_present
#print axioms update_tree_present
#print axioms canonical_inside
end DuplicatePrefix.TypedRetagEntry

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.TypedRetagEntry.canonical_retag_pointer,
      ``DuplicatePrefix.TypedRetagEntry.canonical_retag_place,
      ``DuplicatePrefix.TypedRetagEntry.canonical_reborrow,
      ``DuplicatePrefix.TypedRetagEntry.canonical_new_permission,
      ``DuplicatePrefix.TypedRetagEntry.canonical_size,
      ``DuplicatePrefix.TypedRetagEntry.canonical_inside,
      ``DuplicatePrefix.TypedRetagEntry.machine_retag_enabled] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
