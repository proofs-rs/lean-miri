import duplicate_prefix.TypedRetagEntry
import duplicate_prefix.TypedRetagEmpty
import duplicate_prefix.ProtectedTagsFacts

/-! Canonical FnEntry retagging over the actual arbitrary global tag supply. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.TypedRetagGeneric
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedRetagEntry

def allocatedGlobal (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615) : GlobalState :=
  {global with nextPointerTag := TypedRetagEmpty.successorTag global.nextPointerTag fresh}

def protectedGlobal (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615) : GlobalState :=
  {allocatedGlobal global fresh with protectedTags := global.protectedTags.insert global.nextPointerTag .StrongProtector}

def protectedFrame (frame : FrameState) (id : AllocId) (child : BorTag) : FrameState :=
  frame.addProtector id child

def entryState {K U : Type} (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (global : GlobalState) (fresh : global.nextPointerTag.value < 18446744073709551615) : MachineHooks.State K U :=
  {ambient with
    stack := ⟨frames.push (frameWithBorrow frame borrowFrame)⟩
    machine := {ambient.machine with borrowTracker := some ⟨allocatedGlobal global fresh, .FnEntry⟩}}

def beforeTagState {K U : Type} (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (global : GlobalState) : MachineHooks.State K U :=
  {ambient with
    stack := ⟨frames.push (frameWithBorrow frame borrowFrame)⟩
    machine := {ambient.machine with borrowTracker := some ⟨global, .FnEntry⟩}}

def protectedState {K U : Type} (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615) : MachineHooks.State K U :=
  {ambient with
    stack := ⟨frames.push (frameWithBorrow frame (protectedFrame borrowFrame id global.nextPointerTag))⟩
    machine := {ambient.machine with borrowTracker := some ⟨protectedGlobal global fresh, .FnEntry⟩}}

abbrev childTree (root child : BorTag) (capacity offset len : UInt64) :=
  BorrowRangeAccess.canonicalChildTree root child
    (BorrowRangeAccess.partitionWithInside capacity offset (offset + len)
      BorrowRangeAccess.rootLocation (BorrowRangeAccess.childLocation false))

def completedState {K U : Type} (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (root : BorTag)
    (global : GlobalState) (fresh : global.nextPointerTag.value < 18446744073709551615)
    (capacity offset len : UInt64) : MachineHooks.State K U :=
  {protectedState ambient frames frame borrowFrame id global fresh with machine :=
    {(protectedState ambient frames frame borrowFrame id global fresh).machine with
      memory := RetagEntry.updatedMemory ambient.machine.memory id entry
        (childTree root global.nextPointerTag capacity offset len)}}

def retaggedPlace (place : MPlaceTy Provenance) (id : AllocId) (child : BorTag) : MPlaceTy Provenance :=
  {place with mplace := {place.mplace with ptr := {place.mplace.ptr with provenance := some (.concrete id child)}}}

theorem register_child_protector (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (frame : FrameState) :
    (allocatedGlobal global fresh).addProtector frame id global.nextPointerTag .StrongProtector =
      (protectedGlobal global fresh, protectedFrame frame id global.nextPointerTag) := by rfl

theorem current_frame_entry {K U : Type} (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (global : GlobalState) (fresh : global.nextPointerTag.value < 18446744073709551615) :
    MachineHooks.currentFrame (entryState ambient frames frame borrowFrame global fresh) =
      .ok (frameWithBorrow frame borrowFrame) (entryState ambient frames frame borrowFrame global fresh) := by
  exact current_frame_pushed _ frames _ rfl

/-- The presentation used by the entry theorem is exactly the existing
machine state when its actual stack and tracker fields have these values. -/
theorem before_tag_eq {K U : Type} (state : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (global : GlobalState)
    (stack : state.stack.frames = frames.push frame)
    (borrow : frame.extra.borrowTracker = some borrowFrame)
    (tracker : state.machine.borrowTracker = some ⟨global, .FnEntry⟩) :
    beforeTagState state frames frame borrowFrame global = state := by
  have sameFrame : frameWithBorrow frame borrowFrame = frame := by
    unfold frameWithBorrow
    rw [← borrow]
  unfold beforeTagState
  rw [sameFrame, ← stack, ← tracker]

private theorem reborrow_stage {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity offset len : UInt64)
    (rootTag : BorTag) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : rootTag ≠ global.nextPointerTag)
    (rootUnprotected : global.protectedTags.contains rootTag = false)
    (check : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len)
      (entryState ambient frames frame borrowFrame global fresh) =
      .ok () (entryState ambient frames frame borrowFrame global fresh))
    (resolve : h.resolveAllocation place.mplace.ptr
      (entryState ambient frames frame borrowFrame global fresh) =
      .ok (some ⟨id, Size.ofBytes offset, .concrete rootTag⟩)
        (entryState ambient frames frame borrowFrame global fresh))
    (log : h.logCreation place (Size.ofBytes len) ChildBorrow.fnEntryPolicy global.nextPointerTag
      (some ⟨id, Size.ofBytes offset, .concrete rootTag⟩) = pure ())
    (inside : typed_inside h budget place (Size.ofBytes len) ChildBorrow.fnEntryPolicy =
      pure (DedupRangeMap.new (Size.ofBytes len) ChildBorrow.fnEntryLocation))
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (extraWiring : h.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view =>
      {view with machine := {view.machine with memory}})
    (present : ambient.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes capacity))
    (positive : (0 : UInt64) < len)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (race : ambient.machine.dataRace = none) :
    TypedRetag.reborrow h budget place (Size.ofBytes len) ChildBorrow.fnEntryPolicy
      global.nextPointerTag (entryState ambient frames frame borrowFrame global fresh) =
      .ok (some (.concrete id global.nextPointerTag))
        {protectedState ambient frames frame borrowFrame id global fresh with machine :=
          {(protectedState ambient frames frame borrowFrame id global fresh).machine with
            memory := RetagEntry.updatedMemory ambient.machine.memory id entry
              (childTree rootTag global.nextPointerTag capacity offset len)}} := by
  unfold TypedRetag.reborrow
  simp only [bind, EStateM.bind, check, resolve, log, pure, EStateM.pure]
  simp only [ChildBorrow.fnEntryPolicy]
  simp only [bind, EStateM.bind]
  rw [current_frame_entry]
  simp only [frameWithBorrow]
  unfold_typed ".TypedRetag.tracker"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, entryState]
  simp only [register_child_protector]
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
    (protectedState ambient frames frame borrowFrame id global fresh) id entry present
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
  have rootTree := get_tree_present (protectedState ambient frames frame borrowFrame id global fresh)
    id entry present
  erw [rootTree]
  simp only [bind, EStateM.bind, pure, EStateM.pure, root]
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, protectedState, protectedGlobal,
    ProtectedTags.insert, Array.filter_empty, Array.push_empty]
  have rootStillUnprotected : (protectedGlobal global fresh).protectedTags.contains rootTag = false := by
    change (global.protectedTags.insert global.nextPointerTag .StrongProtector).contains rootTag = false
    simp only [ProtectedTags.contains]
    rw [ProtectedTagsFacts.insert_preserves_other global.protectedTags rootTag global.nextPointerTag
      .StrongProtector distinct]
    exact rootUnprotected
  have parentAccess := ParentBorrowAccess.parent_range_result rootTag capacity offset len .Read
    (protectedGlobal global fresh).protectedTags rootStillUnprotected positive bounds
  simp only [protectedGlobal, ProtectedTags.insert, Array.filter_empty, Array.push_empty] at parentAccess
  erw [parentAccess.1, parentAccess.2]
  let parentTree := {BorrowTree.new rootTag (Size.ofBytes capacity) with
    locations := RangeMapNonempty.intervalPartition capacity offset (offset + len)
      BorrowRangeAccess.rootLocation}
  have parentStored := update_tree_present (protectedState ambient frames frame borrowFrame id global fresh)
    id entry parentTree present
  erw [parentStored]
  have completedSelf : (BorrowTree.BorrowTreeAccessStatus.Completed != .Completed) = false := rfl
  simp only [completedSelf, Bool.false_eq_true, ↓reduceIte, bind, EStateM.bind,
    pure, EStateM.pure, bne_iff_ne, ite_eq_left nonzero]
  let parentState := {protectedState ambient frames frame borrowFrame id global fresh with machine :=
    {(protectedState ambient frames frame borrowFrame id global fresh).machine with
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
    rootTag global.nextPointerTag distinct capacity offset len positive bounds
  simp only [DedupRangeMap.new, Size.ofBytes, beq_iff_eq, nonzero, ↓reduceIte,
    ChildBorrow.fnEntryLocation] at childStep
  erw [childStep]
  have childStored := update_tree_present parentState id
    {entry with allocation := entry.allocation.setExtra parentTree}
    (childTree rootTag global.nextPointerTag capacity offset len) parentPresent
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
    (rootTag : BorTag) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : rootTag ≠ global.nextPointerTag)
    (rootUnprotected : global.protectedTags.contains rootTag = false)
    (pointer : place.mplace.ptr =
      Pointer.new (some (.concrete id rootTag)) (Size.ofBytes (base + offset)))
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
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (race : ambient.machine.dataRace = none) :
    let h := EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
    TypedRetag.reborrow h budget place (Size.ofBytes len) ChildBorrow.fnEntryPolicy
      global.nextPointerTag (entryState ambient frames frame borrowFrame global fresh) =
      .ok (some (.concrete id global.nextPointerTag))
        {protectedState ambient frames frame borrowFrame id global fresh with machine :=
          {(protectedState ambient frames frame borrowFrame id global fresh).machine with
            memory := RetagEntry.updatedMemory ambient.machine.memory id entry
              (childTree rootTag global.nextPointerTag capacity offset len)}} := by
  let h := EvalRetagMachine.hooks prepared runtime
    (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
  have checked : h.checkPtrAccess place.mplace.ptr (Size.ofBytes len)
      (entryState ambient frames frame borrowFrame global fresh) =
      .ok () (entryState ambient frames frame borrowFrame global fresh) := by
    change ValidityMachine.checkPointerAccess access place.mplace.ptr (Size.ofBytes len) _ = _
    rw [pointer]
    exact RetagPointerChecks.check_pointer_access_cached pointers access
      (entryState ambient frames frame borrowFrame global fresh) id rootTag base offset len entry
      pointerWiring width cached present positive signedFits (by simpa only [allocationSize, Size.ofBytes] using bounds)
  have resolved : h.resolveAllocation place.mplace.ptr
      (entryState ambient frames frame borrowFrame global fresh) =
      .ok (some ⟨id, Size.ofBytes offset, .concrete rootTag⟩)
        (entryState ambient frames frame borrowFrame global fresh) := by
    change TypedValidityProviders.resolveAllocation pointers place.mplace.ptr _ = _
    rw [pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers
      (entryState ambient frames frame borrowFrame global fresh) id rootTag base offset width cached
  exact reborrow_stage h budget place ambient frames frame borrowFrame id entry capacity offset len
    rootTag global fresh distinct rootUnprotected checked resolved (by rfl)
    (canonical_inside prepared runtime compiler access projection vtable pointers choice budget place
      (Size.ofBytes len) frozen) globalKind globals extraWiring synchronize present root positive bounds race

private theorem retag_place_stage {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity offset len : UInt64)
    (rootTag : BorTag) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (size : h.sizeAndAlign place = pure (some (Size.ofBytes len, Align.ONE)))
    (provenance : place.mplace.ptr.provenance = some (.concrete id rootTag))
    (reborrow : TypedRetag.reborrow h budget place (Size.ofBytes len) ChildBorrow.fnEntryPolicy
      global.nextPointerTag (entryState ambient frames frame borrowFrame global fresh) =
      .ok (some (.concrete id global.nextPointerTag))
        (completedState ambient frames frame borrowFrame id entry rootTag global fresh capacity offset len)) :
    TypedRetag.retagPlace h budget place ChildBorrow.fnEntryPolicy
      (beforeTagState ambient frames frame borrowFrame global) =
      .ok (retaggedPlace place id global.nextPointerTag)
        (completedState ambient frames frame borrowFrame id entry rootTag global fresh capacity offset len) := by
  unfold TypedRetag.retagPlace
  simp only [size, bind, EStateM.bind, pure, EStateM.pure, Option.map_some, Option.getD_some]
  unfold_typed ".TypedRetag.tracker"
  unfold_typed ".TypedRetag.checked"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, beforeTagState, TypedRetagEmpty.allocate_tag global fresh]
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
    (rootTag : BorTag) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : rootTag ≠ global.nextPointerTag)
    (rootUnprotected : global.protectedTags.contains rootTag = false)
    (pointer : place.mplace.ptr =
      Pointer.new (some (.concrete id rootTag)) (Size.ofBytes (base + offset)))
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
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (slice : SliceFacts projection choice place len)
    (race : ambient.machine.dataRace = none) :
    let h := EvalRetagMachine.hooks prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
    TypedRetag.retagPlace h budget place ChildBorrow.fnEntryPolicy
      (beforeTagState ambient frames frame borrowFrame global) =
      .ok (retaggedPlace place id global.nextPointerTag)
        (completedState ambient frames frame borrowFrame id entry rootTag global fresh capacity offset len) := by
  have provenance : place.mplace.ptr.provenance = some (.concrete id rootTag) := by
    rw [pointer]
    rfl
  exact retag_place_stage _ budget place ambient frames frame borrowFrame id entry capacity offset len rootTag global fresh
    (canonical_size prepared runtime compiler access projection vtable pointers choice place len slice)
    provenance
    (canonical_reborrow prepared runtime compiler access projection vtable pointers choice budget place
      ambient frames frame borrowFrame id entry capacity base offset len rootTag global fresh distinct rootUnprotected pointer frozen pointerWiring width
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
    (rootTag : BorTag) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : rootTag ≠ global.nextPointerTag)
    (rootUnprotected : global.protectedTags.contains rootTag = false)
    (pointer : place.mplace.ptr =
      Pointer.new (some (.concrete id rootTag)) (Size.ofBytes (base + offset)))
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
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes capacity))
    (allocationSize : entry.allocation.byteSize = Size.ofBytes capacity)
    (positive : (0 : UInt64) < len) (signedFits : len.toNat < 9223372036854775808)
    (bounds : offset.toNat + len.toNat ≤ capacity.toNat)
    (slice : SliceFacts projection choice place len)
    (placeShape : place = RetagReferencePlace.slicePlace
      (Pointer.new (.concrete id rootTag) (Size.ofBytes (base + offset))) len place.layout)
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
        (Pointer.new (.concrete id rootTag) (Size.ofBytes (base + offset))) len reference)
      reference.ty .FnEntry (beforeTagState ambient frames frame borrowFrame global) =
      .ok (some (RetagReferencePlace.sliceValue access.runtime.base
        (Pointer.new (.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))) len reference))
        (completedState ambient frames frame borrowFrame id entry rootTag global fresh capacity offset len) := by
  let h := EvalRetagMachine.hooks prepared runtime
    (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
  let oldPointer := Pointer.new (Provenance.concrete id rootTag) (Size.ofBytes (base + offset))
  let newPointer := Pointer.new (Provenance.concrete id global.nextPointerTag) (Size.ofBytes (base + offset))
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
    place.layout.ty (beforeTagState ambient frames frame borrowFrame global) frames
    (frameWithBorrow frame borrowFrame) rfl unpin unsafeUnpin frozen
  have construct : h.immPtrToMPlace value = pure place := by
    change PointerPlaceMachine.fromImmediate access (CompilerExecutionProviders.pointerCompiler prepared)
      choice value = pure place
    exact Eq.trans (RetagReferencePlace.canonical_from_immediate access prepared choice oldPointer len
      reference place.layout dereference pointeeLayout pointeeAlign) (congrArg pure placeShape.symm)
  have changed : retaggedPlace place id global.nextPointerTag = RetagReferencePlace.slicePlace newPointer len place.layout := by
    rw [placeShape]
    rfl
  have reconstruct : h.reconstruct value (retaggedPlace place id global.nextPointerTag) = pure output := by
    rw [changed]
    exact RetagReferencePlace.canonical_reconstruct prepared runtime
      (CompilerRetagOptions.make compiler ⟨false, false⟩) access projection vtable pointers choice
      value newPointer len place.layout
  exact retag_pointer_stage h budget value output place (retaggedPlace place id global.nextPointerTag) place.layout.ty
    (beforeTagState ambient frames frame borrowFrame global)
    (completedState ambient frames frame borrowFrame id entry rootTag global fresh capacity offset len)
    shape pointee policy construct
    (canonical_retag_place prepared runtime compiler access projection vtable pointers choice budget place
      ambient frames frame borrowFrame id entry capacity base offset len rootTag global fresh distinct rootUnprotected pointer frozen pointerWiring width
      globalKind globals extraWiring synchronize cached present root allocationSize positive signedFits bounds slice race)
    reconstruct


#print axioms canonical_retag_pointer
#print axioms canonical_retag_place
#print axioms canonical_reborrow
end DuplicatePrefix.TypedRetagGeneric

open Lean Elab Command in
run_cmd do
  for declaration in #[``DuplicatePrefix.TypedRetagGeneric.canonical_retag_pointer,
      ``DuplicatePrefix.TypedRetagGeneric.canonical_retag_place,
      ``DuplicatePrefix.TypedRetagGeneric.canonical_reborrow] do
    for dependency in (← collectAxioms declaration) do
      unless #[``propext, ``Quot.sound, ``Classical.choice].contains dependency do
        throwError "{declaration} depends on unapproved axiom {dependency}"
