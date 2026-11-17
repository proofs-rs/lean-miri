import duplicate_prefix.TypedRetagGeneric

/-! Empty slices carrying concrete provenance follow the actual lazy-child path. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
namespace DuplicatePrefix.TypedRetagConcreteEmpty
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedRetagEntry

abbrev lazyTree (root child : BorTag) (capacity : UInt64) :=
  BorrowRangeAccess.canonicalChildTree root child
    (DedupRangeMap.new (Size.ofBytes capacity) BorrowRangeAccess.rootLocation)

private theorem zero_reborrow_stage {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (ambient : MachineHooks.State K U)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (capacity offset : UInt64)
    (rootTag : BorTag) (global : GlobalState)
    (fresh : global.nextPointerTag.value < 18446744073709551615)
    (distinct : rootTag ≠ global.nextPointerTag)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO
      (TypedRetagGeneric.entryState ambient frames frame borrowFrame global fresh) =
      .ok () (TypedRetagGeneric.entryState ambient frames frame borrowFrame global fresh))
    (resolve : h.resolveAllocation place.mplace.ptr
      (TypedRetagGeneric.entryState ambient frames frame borrowFrame global fresh) =
      .ok (some ⟨id, Size.ofBytes offset, .concrete rootTag⟩)
        (TypedRetagGeneric.entryState ambient frames frame borrowFrame global fresh))
    (log : h.logCreation place Size.ZERO ChildBorrow.fnEntryPolicy global.nextPointerTag
      (some ⟨id, Size.ofBytes offset, .concrete rootTag⟩) = pure ())
    (inside : typed_inside h budget place Size.ZERO ChildBorrow.fnEntryPolicy =
      pure (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation))
    (globalKind : K)
    (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (extraWiring : h.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view =>
      {view with machine := {view.machine with memory}})
    (present : ambient.machine.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (root : entry.allocation.extra = BorrowTree.new rootTag (Size.ofBytes capacity))
    :
    TypedRetag.reborrow h budget place Size.ZERO ChildBorrow.fnEntryPolicy
      global.nextPointerTag (TypedRetagGeneric.entryState ambient frames frame borrowFrame global fresh) =
      .ok (some (.concrete id global.nextPointerTag))
        {TypedRetagGeneric.protectedState ambient frames frame borrowFrame id global fresh with machine :=
          {(TypedRetagGeneric.protectedState ambient frames frame borrowFrame id global fresh).machine with
            memory := RetagEntry.updatedMemory ambient.machine.memory id entry
              (lazyTree rootTag global.nextPointerTag capacity)}} := by
  unfold TypedRetag.reborrow
  simp only [bind, EStateM.bind, check, resolve, log, pure, EStateM.pure]
  simp only [ChildBorrow.fnEntryPolicy]
  simp only [bind, EStateM.bind]
  rw [TypedRetagGeneric.current_frame_entry]
  simp only [frameWithBorrow]
  unfold_typed ".TypedRetag.tracker"
  simp only [get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind,
    pure, EStateM.pure, TypedRetagGeneric.entryState]
  simp only [TypedRetagGeneric.register_child_protector]
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
    (TypedRetagGeneric.protectedState ambient frames frame borrowFrame id global fresh) id entry present
  erw [ensure]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  simp only [Size.ZERO, Size.ofBytes, DedupRangeMap.new, DedupRangeMap.iterAll,
    beq_iff_eq, ↓reduceIte, ← Array.forIn_toList, List.forIn_nil,
    bind, EStateM.bind, pure, EStateM.pure]
  have tree := get_tree_present (TypedRetagGeneric.protectedState ambient frames frame borrowFrame id global fresh)
    id entry present
  erw [tree]
  simp only [bind, EStateM.bind, pure, EStateM.pure, root]
  have child := ChildConstructor.new_child_zero_exact rootTag global.nextPointerTag distinct capacity offset
  have emptyInside : DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation = {} := by rfl
  rw [emptyInside] at child
  erw [child]
  have stored := update_tree_present (TypedRetagGeneric.protectedState ambient frames frame borrowFrame id global fresh)
    id entry (lazyTree rootTag global.nextPointerTag capacity) present
  erw [stored]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  rfl

end DuplicatePrefix.TypedRetagConcreteEmpty
