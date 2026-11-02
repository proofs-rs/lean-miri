import duplicate_prefix.WildcardHitPoolRoot
import duplicate_prefix.ConcretePoolReferenceBorrow

namespace DuplicatePrefix.MissingConcreteParentRetag
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures Miri.TreeBorrows Miri.Input Miri.Interpreter
open Miri.TreeBorrows.Tree
open TypedRetagEntry TypedBorrowSteps
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
attribute [local irreducible] UniValMap.insert

/-- Missing concrete parents are checked AFTER consuming the actual allocator
slot, and BEFORE examining inside permissions. In particular an empty inside
map does not fall back to a wildcard root or a successful no-op. -/
theorem child (tree : BorrowTree) (slot : WildcardHitPoolRoot.Slot tree)
    (parentTag tag : BorTag) (fresh : GeneralBorrowTagMap.Fresh tree.tagMapping tag)
    (missing : tree.tagMapping.get parentTag = none) (offset : Size)
    (inside : DedupRangeMap LocationState) (outside : Permission) (isProtected : Bool) :
    tree.newChild offset (.concrete parentTag) tag inside outside isProtected =
      ⟨{tree with tagMapping := slot.mapping tag},.error (.MissingParentTag parentTag)⟩ := by
  cases slot with
  | append noFree _aligned fits =>
    unfold BorrowTree.newChild
    rw [GeneralBorrowTagMap.insert_append tree.tagMapping tag fresh noFree fits]
    simp only [missing,Option.map_none,Id.run,pure,Bool.false_eq_true,↓reduceIte]
    rfl
  | reuse index available _bounded _vacant =>
    unfold BorrowTree.newChild
    rw [GeneralBorrowTagMap.insert_free tree.tagMapping tag fresh index available]
    simp only [missing,Option.map_none,Id.run,pure,Bool.false_eq_true,↓reduceIte]
    rfl

/-- Exact typed zero FnEntry failure for an existing live allocation but absent
concrete parent tag. All pointer/allocator/source operations are derived from
initial rows and dictionary identities. The new protector AND consumed tag map
remain committed in the error state. This is invalidProgram, not NoUB or a
successful return; reachability from valid Rust histories is a separate task. -/
theorem reborrow {K U C F A : Type} [DecidableEq K]
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
    (enabled : machine.borrowTracker = some tracker) (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (base offset : UInt64) (parentTag tag : BorTag)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes (base+offset)))
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (present : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (slot : WildcardHitPoolRoot.Slot entry.allocation.extra)
    (fresh : GeneralBorrowTagMap.Fresh entry.allocation.extra.tagMapping tag)
    (missing : entry.allocation.extra.tagMapping.get parentTag = none)
    (frozen : h.typeIsFreeze place.layout.ty = pure true)
    (globalKind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extraWiring : pointers.ensureTreeExtra = GlobalAllocationMachine.ensure globalKind globals)
    (synchronize : globals.synchronizeMemory = fun memory view => {view with machine := {view.machine with memory}}) :
    let changed := {entry.allocation.extra with tagMapping := slot.mapping tag}
    TypedRetag.reborrow h budget place Size.ZERO ChildBorrow.fnEntryPolicy tag (Storage.withCurrent frames frame machine) =
      .error (.invalidProgram s!"reborrow child insertion: {reprStr (BorrowTree.ChildInsertError.MissingParentTag parentTag)}")
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          {registeredMachine machine tracker tag with memory := RetagEntry.updatedMemory machine.memory id entry changed}) := by
  dsimp only
  let start := Storage.withCurrent frames frame machine
  let registered := registeredState frames frame borrowFrame machine tracker id tag
  let changed := {entry.allocation.extra with tagMapping := slot.mapping tag}
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO start = .ok () start := by
    rw [sources.check]
    exact RetagPointerChecks.check_pointer_zero access place.mplace.ptr start
  have resolve : h.resolveAllocation place.mplace.ptr start = .ok (some ⟨id,Size.ofBytes offset,.concrete parentTag⟩) start := by
    rw [sources.resolve,pointer]
    exact RetagPointerChecks.resolve_allocation_cached pointers start id parentTag base offset width cached
  have inside := TypedRetagPolicyFields.inside_for_policy h budget place Size.ZERO ChildBorrow.fnEntryPolicy ChildBorrow.fnEntryLocation
    (ChildBorrow.mutable_fn_entry_initial_location true) sources.precise frozen
  have info := MemoryCopyBridge.live_alloc_info machine.memory id entry present
  have failed := child entry.allocation.extra slot parentTag tag fresh missing (Size.ofBytes offset)
    (DedupRangeMap.new Size.ZERO ChildBorrow.fnEntryLocation) (.ReservedFrz false) true
  dsimp only [start] at check resolve
  unfold TypedRetag.reborrow
  simp only [check,resolve,sources.log,ChildBorrow.fnEntryPolicy,bind,EStateM.bind,pure,EStateM.pure]
  rw [current_frame_pushed start frames frame rfl]
  simp only [frameBorrow,bind,EStateM.bind,pure,EStateM.pure]
  unfold_typed ".TypedRetag.tracker"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,start,Storage.withCurrent,enabled]
  simp only [GlobalState.addProtector,FrameState.addProtector,modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    MachineHooks.setCurrentFrame,get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,set,EStateM.set,
    Array.isEmpty_push,Array.pop_push,Bool.false_eq_true,↓reduceIte]
  unfold_typed ".TypedRetag.checked"
  simp only [info,bind,EStateM.bind,pure,EStateM.pure]
  have liveKind : (AllocationKind.liveData != .liveData) = false := rfl
  simp only [liveKind,Bool.false_eq_true,↓reduceIte]
  erw [inside]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  rw [sources.ensure,extraWiring]
  erw [RetagPointerChecks.ensure_tree_live globalKind globals synchronize registered id entry present]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  simp only [Size.ZERO,Size.ofBytes,DedupRangeMap.new,DedupRangeMap.iterAll,beq_self_eq_true,↓reduceIte,
    ←Array.forIn_toList,List.forIn_nil,bind,EStateM.bind,pure,EStateM.pure]
  erw [get_tree_present registered id entry present]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  erw [failed]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  erw [update_tree_present registered id entry changed present]
  rfl

end DuplicatePrefix.MissingConcreteParentRetag
