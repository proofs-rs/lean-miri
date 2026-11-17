import duplicate_prefix.TypedBorrowSteps

/-! Composition at the actual protected retag ensure phase. The ensure equation
is an internal execution lemma; it is not an input-validity premise. The saved
child tag precedes conversion and need not be adjacent to the final counter. -/
namespace DuplicatePrefix.CurrentCallTypedAfterEnsure
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
open TypedRetagEntry TypedBorrowSteps
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true
open Lean Elab in
private def helper (suffix : String) : CoreM Name := do
  let names := (← getEnv).constants.toList.filterMap fun (name, _) =>
    if name.toString.endsWith suffix then some name else none
  match names with
  | [name] => pure name
  | _ => throwError "expected exact source helper {suffix}"
open Lean Elab in
elab "after_ensure_rule " suffix:str : term => do
  Lean.Meta.mkConstWithFreshMVarLevels (← helper suffix.getString)

theorem protected_reborrow {K U : Type} [DecidableEq K]
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
    (info : machine.memory.getAllocInfo id =
      .ok ⟨entry.allocation.byteSize, entry.allocation.align, .liveData, entry.allocation.mutability⟩)
    (after : MachineHooks.MachineState K U) (afterTracker : MachineHooks.BorrowState)
    (ensure : h.ensureTreeExtra id (registeredState frames frame borrowFrame machine tracker id tag) =
      .ok () (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag) after))
    (afterEnabled : after.borrowTracker = some afterTracker)
    (present : after.memory.live.find? (fun row => row.1 == id) = some (id, entry))
    (race : after.dataRace = none) (parentTree finalTree : BorrowTree)
    (readTree : (entry.allocation.extra.performBorrowAccessRange parent (Size.ofBytes offset)
      (Size.ofBytes len) .Read afterTracker.global.protectedTags .VisitChildrenOfAccessed).tree = parentTree)
    (readDone : (entry.allocation.extra.performBorrowAccessRange parent (Size.ofBytes offset)
      (Size.ofBytes len) .Read afterTracker.global.protectedTags .VisitChildrenOfAccessed).status = .Completed)
    (child : parentTree.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new (Size.ofBytes len) initial) policy.outsidePermission policy.protector.isSome =
      ⟨finalTree, .ok ()⟩) :
    TypedRetag.reborrow h budget place (Size.ofBytes len) policy tag (Storage.withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag)
          {after with memory := RetagEntry.updatedMemory after.memory id entry finalTree}) := by
  let start := Storage.withCurrent frames frame machine
  unfold TypedRetag.reborrow
  simp only [check, resolve, log, bind, EStateM.bind, pure, EStateM.pure]
  rw [protection]
  simp only [bind, EStateM.bind]
  rw [current_frame_pushed start frames frame rfl]
  simp only [frameBorrow, bind, EStateM.bind, pure, EStateM.pure]
  erw [(after_ensure_rule ".TypedBorrowSteps.tracker_present") start tracker enabled]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  simp only [GlobalState.addProtector, FrameState.addProtector, modify, modifyGet,
    MonadStateOf.modifyGet, EStateM.modifyGet, MachineHooks.setCurrentFrame,
    get, getThe, MonadStateOf.get, EStateM.get, bind, EStateM.bind, pure, EStateM.pure,
    set, EStateM.set, start, Storage.withCurrent, Array.isEmpty_push, Array.pop_push,
    Bool.false_eq_true, ↓reduceIte]
  unfold_typed ".TypedRetag.checked"
  simp only [info, bind, EStateM.bind, pure, EStateM.pure]
  have liveDataSelf : (AllocationKind.liveData != .liveData) = false := rfl
  simp only [liveDataSelf, Bool.false_eq_true, ↓reduceIte]
  erw [inside]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  erw [ensure]
  simp only [bind, EStateM.bind, pure, EStateM.pure]
  let selectedPolicy := {policy with protector := some .StrongProtector}
  change (after_ensure_rule ".TypedBorrowSteps.readInsert") h ⟨id, Size.ofBytes offset, parent⟩
    (DedupRangeMap.new (Size.ofBytes len) initial) selectedPolicy tag
    (Storage.withCurrent frames (registeredFrame frame borrowFrame id tag) after) = _
  have selectedChild : parentTree.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new (Size.ofBytes len) initial) selectedPolicy.outsidePermission selectedPolicy.protector.isSome =
      ⟨finalTree, .ok ()⟩ := by simpa only [selectedPolicy, protection] using child
  exact (after_ensure_rule ".TypedBorrowSteps.read_insert_steps") h frames (registeredFrame frame borrowFrame id tag)
    after afterTracker afterEnabled id entry offset len parent tag
    initial selectedPolicy associated positive present race parentTree finalTree readTree readDone selectedChild

end DuplicatePrefix.CurrentCallTypedAfterEnsure
