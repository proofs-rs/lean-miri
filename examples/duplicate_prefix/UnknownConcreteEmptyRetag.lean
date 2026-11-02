import duplicate_prefix.TypedBorrowSteps

namespace DuplicatePrefix.UnknownConcreteEmptyRetag
open Miri.ABI Miri.Memory Miri.MIR Miri.DataStructures
open Miri.TreeBorrows Miri.Input Miri.Interpreter
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
set_option backward.dsimp.instances true

/-- An absent ID in every actual metadata source is an explicit lookup error.
Zero length does not fabricate allocation metadata. -/
theorem missing_info {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (live : memory.live.find? (fun row => row.1 == id) = none)
    (function : memory.hasFunctionPointer id = false)
    (vaList : memory.hasVaListId id = false)
    (global : memory.findGlobal? id = none)
    (dead : memory.dead.find? (fun row => row.allocId == id) = none) :
    memory.getAllocInfo id = .error (.unavailable id) := by
  unfold MemoryState.hasVaListId at vaList
  simp only [MemoryState.getAllocInfo,live,function,global,dead,vaList,
    Bool.false_eq_true,↓reduceIte]
  rfl

/-- Actual typed reborrow rejects unknown concrete allocation metadata even for
an empty reference. Pointer check and resolution are DERIVED from source dictionary
identities and the cached address, not supplied as successful outcomes. The
policy has no protector, so this error leaves the exact initial state untouched.
This is an invalidProgram boundary, not a successful invocation or a NoUB claim. -/
theorem unprotected {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (checkWiring : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (resolveWiring : h.resolveAllocation = TypedValidityProviders.resolveAllocation pointers)
    (logWiring : h.logCreation = fun _ _ _ _ _ => pure ())
    (budget : Nat) (place : MPlaceTy Provenance) (state : ValidityMachine.State K U)
    (policy : RetagPolicy.NewPermission) (unprotected : policy.protector = none)
    (id : AllocId) (parent tag : BorTag) (base offset : UInt64)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parent)) (Size.ofBytes (base+offset)))
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : state.machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : state.machine.memory.live.find? (fun row => row.1 == id) = none)
    (function : state.machine.memory.hasFunctionPointer id = false)
    (vaList : state.machine.memory.hasVaListId id = false)
    (global : state.machine.memory.findGlobal? id = none)
    (dead : state.machine.memory.dead.find? (fun row => row.allocId == id) = none) :
    TypedRetag.reborrow h budget place Size.ZERO policy tag state =
      .error (.invalidProgram s!"allocation kind: {reprStr (AllocationLookupError.unavailable id)}") state := by
  have check := RetagPointerChecks.check_pointer_zero access
    (Pointer.new (some (.concrete id parent)) (Size.ofBytes (base+offset))) state
  have resolve := RetagPointerChecks.resolve_allocation_cached pointers state id parent base offset width cached
  have info := missing_info state.machine.memory id live function vaList global dead
  unfold TypedRetag.reborrow
  rw [checkWiring,resolveWiring,logWiring]
  simp only [pointer,check,resolve,unprotected,bind,EStateM.bind,pure,EStateM.pure]
  unfold_typed ".TypedRetag.checked"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,pure,info]
  rfl


/-- FnEntry installs its real protector BEFORE the missing-metadata failure.
The exact partially modified state is retained; it is not a safe/no-op return. -/
theorem fn_entry {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U))
    (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (checkWiring : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (resolveWiring : h.resolveAllocation = TypedValidityProviders.resolveAllocation pointers)
    (logWiring : h.logCreation = fun _ _ _ _ _ => pure ())
    (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array (Frame Provenance LocalLayout MachineHooks.FrameExtra))
    (frame : Frame Provenance LocalLayout MachineHooks.FrameExtra) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U)) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (policy : RetagPolicy.NewPermission) (protection : policy.protector = some .StrongProtector)
    (id : AllocId) (parent tag : BorTag) (base offset : UInt64)
    (pointer : place.mplace.ptr = Pointer.new (some (.concrete id parent)) (Size.ofBytes (base+offset)))
    (width : pointers.arithmetic = ⟨Size.ofBytes 8⟩)
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live.find? (fun row => row.1 == id) = none)
    (function : machine.memory.hasFunctionPointer id = false)
    (vaList : machine.memory.hasVaListId id = false)
    (global : machine.memory.findGlobal? id = none)
    (dead : machine.memory.dead.find? (fun row => row.allocId == id) = none) :
    TypedRetag.reborrow h budget place Size.ZERO policy tag (Storage.withCurrent frames frame machine) =
      .error (.invalidProgram s!"allocation kind: {reprStr (AllocationLookupError.unavailable id)}")
        (TypedBorrowSteps.registeredState frames frame borrowFrame machine tracker id tag) := by
  let start := Storage.withCurrent frames frame machine
  have check := RetagPointerChecks.check_pointer_zero access
    (Pointer.new (some (.concrete id parent)) (Size.ofBytes (base+offset))) start
  have resolve := RetagPointerChecks.resolve_allocation_cached pointers start id parent base offset width cached
  have info := missing_info machine.memory id live function vaList global dead
  dsimp only [start] at check resolve
  unfold TypedRetag.reborrow
  rw [checkWiring,resolveWiring,logWiring]
  simp only [pointer,check,resolve,bind,EStateM.bind,pure,EStateM.pure]
  rw [protection]
  simp only [EStateM.bind]
  rw [TypedRetagEntry.current_frame_pushed start frames frame rfl]
  simp only [frameBorrow,EStateM.bind]
  unfold_typed ".TypedRetag.tracker"
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,pure,EStateM.pure,start,Storage.withCurrent,enabled]
  simp only [GlobalState.addProtector,FrameState.addProtector,modify,modifyGet,
    MonadStateOf.modifyGet,EStateM.modifyGet,MachineHooks.setCurrentFrame,
    get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
    set,EStateM.set,Array.isEmpty_push,Array.pop_push,Bool.false_eq_true,↓reduceIte]
  unfold_typed ".TypedRetag.checked"
  simp only [info,pure]
  rfl

end DuplicatePrefix.UnknownConcreteEmptyRetag
