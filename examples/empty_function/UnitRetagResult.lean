import empty_function.UnitRetag
import empty_function.ChildSuccess
import Miri.Interpreter.RunLoop

/-! Internal actual-operation composition. Canonical prefix builders discharge
check/resolve/ensure equalities; no such equality is a caller validity field. -/
namespace EmptyFunction.UnitRetagResult
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.Interpreter Miri.Input Miri.TreeBorrows Miri.TreeBorrows.Tree
open EmptyFunction.UnitRetag Miri.DataStructures
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem reborrow_zero_live_ensure_error {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array F) (frame : F) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (offset : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO (withCurrent frames frame machine) =
      .ok () (withCurrent frames frame machine))
    (resolve : h.resolveAllocation place.mplace.ptr (withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩) (withCurrent frames frame machine))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (precise : h.preciseInteriorMut = pure false)
    (freeze : h.typeIsFreeze place.layout.ty = pure true)
    (info : AllocationInfo)
    (classified : machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData)
    (error : StepError) (failedState : MachineHooks.State K U)
    (failed : h.ensureTreeExtra id
      (withCurrent frames (registeredFrame frame borrowFrame id tag) (registeredMachine machine tracker tag)) =
      .error error failedState) :
    TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
      (withCurrent frames frame machine) = .error error failedState := by
  let start := withCurrent frames frame machine
  have current : MachineHooks.currentFrame start = .ok frame start := by
    simp [MachineHooks.currentFrame, Stack.currentFrame?, start, withCurrent,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  unfold TypedRetag.reborrow
  simp only [check,resolve,log,bind,EStateM.bind,pure,EStateM.pure,MachineHooks.protectionPolicy]
  rw [current]
  simp only [frameBorrow,bind,EStateM.bind,pure,EStateM.pure,TypedRetag.tracker_apply]
  simp only [start,withCurrent,enabled,bind,EStateM.bind,pure,EStateM.pure]
  simp only [GlobalState.addProtector,FrameState.addProtector,modify,modifyGet,
    MonadStateOf.modifyGet,EStateM.modifyGet,MachineHooks.setCurrentFrame,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    set,EStateM.set,Array.isEmpty_push,Array.pop_push,Bool.false_eq_true,↓reduceIte]
  simp only [TypedRetag.checked_eq,classified,bind,EStateM.bind,pure,EStateM.pure]
  simp only [data,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  erw [TypedRetag.insidePermissions_unit h budget place precise freeze]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  erw [failed]

theorem reborrow_zero_live_ensured {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array F) (frame : F) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (offset : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO (withCurrent frames frame machine) =
      .ok () (withCurrent frames frame machine))
    (resolve : h.resolveAllocation place.mplace.ptr (withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩) (withCurrent frames frame machine))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (precise : h.preciseInteriorMut = pure false)
    (freeze : h.typeIsFreeze place.layout.ty = pure true)
    (info : AllocationInfo)
    (classified : machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData)
    (ensuredMachine : MachineHooks.MachineState K U)
    (ensured : h.ensureTreeExtra id
      (withCurrent frames (registeredFrame frame borrowFrame id tag) (registeredMachine machine tracker tag)) =
      .ok () (withCurrent frames (registeredFrame frame borrowFrame id tag) ensuredMachine))
    (live : ensuredMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    let child := entry.allocation.extra.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new Size.ZERO ⟨.ReservedFrz false,false,.None⟩) (.ReservedFrz false) true
    let after := withCurrent frames (registeredFrame frame borrowFrame id tag)
      {ensuredMachine with memory := replaceTree ensuredMachine.memory id entry child.tree}
    TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
      (withCurrent frames frame machine) =
      match child.outcome with
      | .ok () => .ok (some (.concrete id tag)) after
      | .error error => .error (.invalidProgram ("reborrow child insertion" ++ ": " ++ reprStr error)) after := by
  let start := withCurrent frames frame machine
  have current : MachineHooks.currentFrame start = .ok frame start := by
    simp [MachineHooks.currentFrame, Stack.currentFrame?, start, withCurrent,
      get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure]
  unfold TypedRetag.reborrow
  simp only [check,resolve,log,bind,EStateM.bind,pure,EStateM.pure,MachineHooks.protectionPolicy]
  rw [current]
  simp only [frameBorrow,bind,EStateM.bind,pure,EStateM.pure,TypedRetag.tracker_apply]
  simp only [start,withCurrent,enabled,bind,EStateM.bind,pure,EStateM.pure]
  simp only [GlobalState.addProtector,FrameState.addProtector,modify,modifyGet,
    MonadStateOf.modifyGet,EStateM.modifyGet,MachineHooks.setCurrentFrame,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,
    set,EStateM.set,Array.isEmpty_push,Array.pop_push,Bool.false_eq_true,↓reduceIte]
  simp only [TypedRetag.checked_eq,classified,bind,EStateM.bind,pure,EStateM.pure]
  simp only [data,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  erw [TypedRetag.insidePermissions_unit h budget place precise freeze]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  erw [ensured]
  simp only [bind,EStateM.bind,pure,EStateM.pure,DedupRangeMap.new,DedupRangeMap.iterAll,
    Size.ZERO,Size.ofBytes,beq_self_eq_true,↓reduceIte,←Array.forIn_toList,List.forIn_nil,
    TypedRetag.getTree_apply]
  simp only [withCurrent,live]
  let child := entry.allocation.extra.newChild (Size.ofBytes offset) parent tag {}
    (.ReservedFrz false) true
  simp only [TypedRetag.updateTree_apply,live]
  erw [set_live ensuredMachine.memory id entry child.tree live]
  simp only [TypedRetag.checked_eq,bind,EStateM.bind,pure,EStateM.pure]
  dsimp only [child]
  simp only [show (some ProtectorKind.StrongProtector).isSome = true from rfl]
  cases outcome : (entry.allocation.extra.newChild (Size.ofBytes offset) parent tag {}
      (.ReservedFrz false) true).outcome with
  | ok value => cases value; simp only [Size.ofBytes] at outcome; simp [outcome,Size.ofBytes,pure,Pure.pure,EStateM.pure] <;> rfl
  | error error => simp only [Size.ofBytes] at outcome; simp [outcome,Size.ofBytes,throw,throwThe,MonadExceptOf.throw,EStateM.throw] <;> rfl

/-- Exact source state after a successful entry-tag reservation. -/
def allocated {K U : Type} (state : MachineHooks.State K U)
    (tracker : MachineHooks.BorrowState) (global : GlobalState) : MachineHooks.State K U :=
  {state with machine := {state.machine with borrowTracker := some {tracker with global}}}

/-- Errors in the zero-size reborrow propagate through the entry protector,
without executing the trailing uninitialized write. -/
theorem protect_of_failed_reborrow {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (global : GlobalState) (tag : BorTag)
    (sizeQuery : h.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (enabled : state.machine.borrowTracker = some tracker)
    (tagged : tracker.global.newPointerTag = .ok (global,tag))
    (error : StepError) (failedState : MachineHooks.State K U)
    (failed : TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
      (allocated state tracker global) = .error error failedState) :
    TypedRetag.protectInPlaceFunctionArgument h budget place state = .error error failedState := by
  unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace TypedRetag.retagPlace
  simp only [enabled,sizeQuery,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    get,getThe,MonadStateOf.get,EStateM.get,Option.isSome_some,↓reduceIte,
    TypedRetag.tracker_apply,TypedRetag.checked_eq,tagged]
  simp only [modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  erw [failed]

/-- Retagging preserves absent provenance; otherwise it installs the returned
borrow provenance. The actual unit write remains a separately proved source edge. -/
def retainedPlace (place : MPlaceTy Provenance) (provenance : Option Provenance) : MPlaceTy Provenance :=
  {place with mplace := {place.mplace with ptr := {place.mplace.ptr with
    provenance := if place.mplace.ptr.provenance.isNone then none else provenance}}}

 theorem protect_of_returned_reborrow {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (state : MachineHooks.State K U) (tracker : MachineHooks.BorrowState)
    (global : GlobalState) (tag : BorTag)
    (sizeQuery : h.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (enabled : state.machine.borrowTracker = some tracker)
    (tagged : tracker.global.newPointerTag = .ok (global,tag))
    (provenance : Option Provenance) (after finished : MachineHooks.State K U)
    (borrowed : TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
      (allocated state tracker global) = .ok provenance after)
    (lossless : place.mplace.ptr.provenance ≠ none → provenance ≠ none)
    (written : h.writeUninit (retainedPlace place provenance) after = .ok () finished) :
    TypedRetag.protectInPlaceFunctionArgument h budget place state = .ok () finished := by
  unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace TypedRetag.retagPlace
  simp only [enabled,sizeQuery,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    get,getThe,MonadStateOf.get,EStateM.get,Option.isSome_some,↓reduceIte,
    TypedRetag.tracker_apply,TypedRetag.checked_eq,tagged]
  simp only [modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  erw [borrowed]
  cases original : place.mplace.ptr.provenance with
  | none => simpa [retainedPlace,original,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure] using written
  | some old =>
    cases provenance with
    | none => exact False.elim (lossless (by simp [original]) rfl)
    | some fresh => simpa [retainedPlace,original,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure] using written

theorem reborrow_zero_live_cases {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array F) (frame : F) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (offset : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO (withCurrent frames frame machine) =
      .ok () (withCurrent frames frame machine))
    (resolve : h.resolveAllocation place.mplace.ptr (withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩) (withCurrent frames frame machine))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (precise : h.preciseInteriorMut = pure false)
    (freeze : h.typeIsFreeze place.layout.ty = pure true)
    (info : AllocationInfo)
    (classified : machine.memory.getAllocInfo id = .ok info)
    (data : info.kind = .liveData)
    (ensuredMachine : MachineHooks.MachineState K U)
    (ensured : h.ensureTreeExtra id
      (withCurrent frames (registeredFrame frame borrowFrame id tag) (registeredMachine machine tracker tag)) =
      .ok () (withCurrent frames (registeredFrame frame borrowFrame id tag) ensuredMachine))
    (live : ensuredMachine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (currentTag : BorTag) (formed : TreeRuntimeInput.TreeFormed entry.allocation.extra currentTag)
    (fresh : entry.allocation.extra.tagMapping.get tag = none)
    (parentPresent : ∀ parentTag, parent = .concrete parentTag →
      ∃ index, entry.allocation.extra.tagMapping.get parentTag = some index)
    (protections : ProtectedTags) :
    (∃ tree, TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
        (withCurrent frames frame machine) =
        .ok (some (.concrete id tag)) (withCurrent frames (registeredFrame frame borrowFrame id tag)
          {ensuredMachine with memory := replaceTree ensuredMachine.memory id entry tree}) ∧
      tree.releaseProtector tag protections = ⟨tree,.Released⟩ ∧
      Preservation.OldNodeRights entry.allocation.extra tree) ∨
    (∃ reason tree, TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
        (withCurrent frames frame machine) =
        .error (.invalidProgram reason) (withCurrent frames (registeredFrame frame borrowFrame id tag)
          {ensuredMachine with memory := replaceTree ensuredMachine.memory id entry tree})) := by
  have actual := reborrow_zero_live_ensured h budget place frames frame borrowFrame machine tracker
    enabled frameBorrow id entry offset parent tag check resolve log precise freeze info classified data
    ensuredMachine ensured live
  let child := entry.allocation.extra.newChild (Size.ofBytes offset) parent tag
    (DedupRangeMap.new Size.ZERO ⟨.ReservedFrz false,false,.None⟩) (.ReservedFrz false) true
  change TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
      (withCurrent frames frame machine) =
    match child.outcome with
    | .ok () => .ok (some (.concrete id tag)) _
    | .error error => .error (.invalidProgram ("reborrow child insertion" ++ ": " ++ reprStr error)) _ at actual
  cases outcome : child.outcome with
  | error error =>
    apply Or.inr
    exact ⟨_,child.tree,by simpa only [outcome] using actual⟩
  | ok value =>
    cases value
    have created : child = ⟨child.tree,.ok ()⟩ := by
      cases current : child with
      | mk tree result =>
        have success : result = .ok () := by simpa only [current] using outcome
        cases success
        rfl
    have certificate : child.tree.releaseProtector tag protections = ⟨child.tree,.Released⟩ ∧
        Preservation.OldNodeRights entry.allocation.extra child.tree := by
      cases parent with
      | wildcard =>
        exact ChildSuccess.wildcard entry.allocation.extra currentTag tag formed fresh
          (Size.ofBytes offset) ⟨.ReservedFrz false,false,.None⟩ child.tree created protections
      | concrete parentTag =>
        obtain ⟨index,tagged⟩ := parentPresent parentTag rfl
        exact ChildSuccess.concrete entry.allocation.extra currentTag tag formed fresh parentTag index tagged
          (Size.ofBytes offset) ⟨.ReservedFrz false,false,.None⟩ child.tree created protections
    exact Or.inl ⟨child.tree,by simpa only [outcome] using actual,certificate⟩

/-- Actual singleton release from the current tracker; source roots/tags created
by materialization are retained, and only end_call removes the child protector. -/
theorem release_live_current {K U : Type} [DecidableEq K]
    (kind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view =
      {view with machine := {view.machine with memory}})
    (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) (tag : BorTag)
    (released : tree.releaseProtector tag tracker.global.protectedTags = ⟨tree,.Released⟩) :
    MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure kind globals)
      (withCurrent frames (registeredFrame frame {} id tag)
        {machine with memory := replaceTree machine.memory id entry tree}) =
      .ok () (withCurrent frames (registeredFrame frame {} id tag)
        {machine with memory := replaceTree machine.memory id entry tree, borrowTracker := some {tracker with global := tracker.global.endCall (({} : FrameState).addProtector id tag)}}) := by
  let updated := {entry with allocation := entry.allocation.setExtra tree}
  let memory := replaceTree machine.memory id entry tree
  let state := withCurrent frames (registeredFrame frame {} id tag)
    {machine with memory}
  have live : memory.live.find? (fun row => row.1 == id) = some (id,updated) :=
    replace_lookup machine.memory id entry tree
  have info : memory.getAllocInfo id =
      .ok ⟨updated.allocation.byteSize,updated.allocation.align,.liveData,updated.allocation.mutability⟩ := by
    simp [MemoryState.getAllocInfo,live]
    rfl
  have ensure := EmptyFunction.UnitProtection.ensure_live kind globals synchronize state id updated live
  have mutation := set_live memory id updated tree live
  have again : replaceTree memory id updated tree = memory := replace_same machine.memory id entry tree
  rw [again] at mutation
  dsimp only [memory] at info
  dsimp only [memory,updated] at live
  dsimp only [state,memory,withCurrent,registeredMachine,registeredFrame,FrameState.addProtector] at ensure
  simp only [enabled] at ensure
  unfold MachineHooks.beforeStackPopWithEnsure
  simp [get,getThe,MonadStateOf.get,EStateM.get,withCurrent,registeredMachine,
    MachineHooks.currentFrame,Stack.currentFrame?,registeredFrame,FrameState.addProtector,enabled,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,info]
  erw [ensure]
  simp [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    withCurrent,registeredFrame,registeredMachine,live,enabled,Allocation.setExtra,Allocation.mapExtra]
  erw [released]
  simp only [Allocation.setExtra,Allocation.mapExtra] at mutation
  erw [mutation]
  simp only [modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    set,MonadStateOf.set,EStateM.set,GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  rfl

open Lean Elab Command in
run_cmd do
  let mut total : Nat := 0
  for (name,_) in (← getEnv).constants.toList do
    if name.toString.startsWith "EmptyFunction.UnitRetagResult." ||
        (name.toString.startsWith "_private." && name.toString.contains "UnitRetagResult") then
      total := total+1
      for dependency in (← collectAxioms name) do
        unless #[``propext,``Quot.sound,``Classical.choice].contains dependency do
          throwError "unapproved zero-retag-result axiom {dependency} in {name}"
  logInfo m!"Audited {total} actual zero-retag declarations"
#print axioms reborrow_zero_live_cases
#print axioms protect_of_failed_reborrow
#print axioms protect_of_returned_reborrow
end EmptyFunction.UnitRetagResult
