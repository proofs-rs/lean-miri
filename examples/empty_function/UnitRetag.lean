import empty_function.UnitProtection
import empty_function.TreeRuntimeInput

/-! Source-level composition of zero-byte protection. Equation-based helpers
are implementation lemmas; the public admission layer must derive their
operation equations from the raw runtime records and canonical dictionaries. -/
namespace EmptyFunction.UnitRetag
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows.Tree
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

abbrev F := Frame Provenance LocalLayout MachineHooks.FrameExtra

def withCurrent {K U : Type} (frames : Array F) (frame : F) (machine : MachineHooks.MachineState K U) :
    MachineHooks.State K U := ⟨⟨frames.push frame⟩,machine⟩

def replaceTree {K : Type} (memory : MemoryState Provenance BorrowTree K) (id : AllocId)
    (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) : MemoryState Provenance BorrowTree K :=
  {memory with live := ((memory.live.filter (fun row => row.1 != id)).push (id,{entry with allocation := entry.allocation.setExtra tree}))}

theorem set_live {K : Type} [DecidableEq K] (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree)
    (live : memory.live.find? (fun row => row.1 == id) = some (id,entry)) :
    memory.setLiveAllocation id (entry.allocation.setExtra tree) = .ok (replaceTree memory id entry tree) := by
  exact MemoryState.setLiveAllocation_of_find memory id entry (entry.allocation.setExtra tree) live

def registeredFrame (frame : F) (borrowFrame : FrameState) (id : AllocId) (tag : BorTag) : F :=
  {frame with extra := {frame.extra with borrowTracker := some (borrowFrame.addProtector id tag)}}

def registeredTracker (tracker : MachineHooks.BorrowState) (tag : BorTag) :=
  {tracker with global := {tracker.global with protectedTags := tracker.global.protectedTags.insert tag .StrongProtector}}

def registeredMachine {K U : Type} (machine : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) (tag : BorTag) :=
  {machine with borrowTracker := some (registeredTracker tracker tag)}

set_option linter.unusedSimpArgs false in
/-- Internal source composition only. The check/resolve/constructor equations
must be discharged by raw-input theorems before this can be used as admission. -/
private theorem reborrow_zero_live_equations {K U : Type} [DecidableEq K]
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
    (kind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (extra : h.ensureTreeExtra = GlobalAllocationMachine.ensure kind globals)
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view =
      {view with machine := {view.machine with memory}})
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (finalTree : BorrowTree)
    (child : entry.allocation.extra.newChild (Size.ofBytes offset) parent tag
      (DedupRangeMap.new Size.ZERO ⟨.ReservedFrz false,false,.None⟩) (.ReservedFrz false) true =
      ⟨finalTree,.ok ()⟩) :
    TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
      (withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (withCurrent frames (registeredFrame frame borrowFrame id tag)
          {registeredMachine machine tracker tag with memory := replaceTree machine.memory id entry finalTree}) := by
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
  have info : machine.memory.getAllocInfo id =
      .ok ⟨entry.allocation.byteSize,entry.allocation.align,.liveData,entry.allocation.mutability⟩ := by
    simp [MemoryState.getAllocInfo,live]
    rfl
  simp only [TypedRetag.checked_eq,info,bind,EStateM.bind,pure,EStateM.pure]
  have liveSelf : (AllocationKind.liveData != .liveData) = false := rfl
  simp only [liveSelf,Bool.false_eq_true,↓reduceIte]
  erw [TypedRetag.insidePermissions_unit h budget place precise freeze]
  simp only [bind,EStateM.bind,pure,EStateM.pure]
  rw [extra]
  have ensured := EmptyFunction.UnitProtection.ensure_live kind globals synchronize
    (withCurrent frames (registeredFrame frame borrowFrame id tag) (registeredMachine machine tracker tag))
    id entry live
  erw [ensured]
  simp only [bind,EStateM.bind,pure,EStateM.pure,DedupRangeMap.new,DedupRangeMap.iterAll,
    Size.ZERO,Size.ofBytes,beq_self_eq_true,↓reduceIte,←Array.forIn_toList,List.forIn_nil,
    TypedRetag.getTree_apply]
  simp only [registeredMachine,registeredTracker,registeredFrame,withCurrent,live]
  rw [show DedupRangeMap.new Size.ZERO (⟨.ReservedFrz false,false,.None⟩ : LocationState) = {} from rfl] at child
  erw [child]
  simp only [TypedRetag.updateTree_apply,live]
  rw [set_live machine.memory id entry finalTree live]
  simp only [TypedRetag.checked_eq,bind,EStateM.bind,pure,EStateM.pure]

/-- Live concrete zero protection from initial raw current-state facts. The
canonical dictionary equations are library adequacy facts; no memory access,
resolution, child construction or release success is a caller hypothesis. -/
theorem reborrow_zero_live_concrete {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat)
    (place : MPlaceTy Provenance) (frames : Array F) (frame : F) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (parentTag tag : BorTag) (parentIndex : UniIndex) (address base : UInt64)
    (encoding : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes address))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : TreeRuntimeInput.TreeFormed entry.allocation.extra tag)
    (tagged : entry.allocation.extra.tagMapping.get parentTag = some parentIndex)
    (room : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (checkBinding : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (resolveBinding : h.resolveAllocation = TypedValidityProviders.resolveAllocation pointers)
    (truncate : ∀ value, pointers.arithmetic.truncateToTargetUsize value = .ok value)
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (precise : h.preciseInteriorMut = pure false)
    (freeze : h.typeIsFreeze place.layout.ty = pure true)
    (kind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extra : h.ensureTreeExtra = GlobalAllocationMachine.ensure kind globals)
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view =
      {view with machine := {view.machine with memory}}) :
    ∃ finalTree,
      TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
        (withCurrent frames frame machine) =
        .ok (some (.concrete id tag))
          (withCurrent frames (registeredFrame frame borrowFrame id tag)
            {registeredMachine machine tracker tag with memory := replaceTree machine.memory id entry finalTree}) ∧
      finalTree.releaseProtector tag (registeredTracker tracker tag).global.protectedTags =
        ⟨finalTree,.Released⟩ := by
  let start := withCurrent frames frame machine
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO start = .ok () start := by
    rw [checkBinding]
    exact EmptyFunction.UnitProtection.check_pointer_zero access place.mplace.ptr start
  have resolve : h.resolveAllocation place.mplace.ptr start =
      .ok (some ⟨id,Size.ofBytes (address-base),.concrete parentTag⟩) start := by
    rw [resolveBinding,encoding]
    exact EmptyFunction.UnitProtection.resolve_concrete pointers id parentTag address base truncate start cached
  obtain ⟨finalTree,child,released⟩ := tree.constructAndRelease parentTag parentIndex tagged room
    (Size.ofBytes (address-base)) ⟨.ReservedFrz false,false,.None⟩
    (registeredTracker tracker tag).global.protectedTags
  exact ⟨finalTree,reborrow_zero_live_equations h budget place frames frame borrowFrame machine tracker enabled
    frameBorrow id entry (address-base) (.concrete parentTag) tag check resolve log precise freeze kind globals extra
    synchronize live finalTree child,released⟩

private theorem successor_nonzero (tag : BorTag) (room : tag.value < 18446744073709551615) :
    tag.value + 1 ≠ 0 := by
  have bound : tag.value.toNat < 18446744073709551615 := UInt64.lt_iff_toNat_lt.mp room
  have fits : tag.value.toNat+1 < 2^64 := by omega
  intro equal
  have impossible := congrArg UInt64.toNat equal
  simp only [UInt64.toNat_add,UInt64.toNat_one,UInt64.toNat_zero,Nat.mod_eq_of_lt fits] at impossible
  omega

def successorTag (tag : BorTag) (room : tag.value < 18446744073709551615) : BorTag :=
  ⟨tag.value+1,successor_nonzero tag room⟩

def allocatedTracker (tracker : MachineHooks.BorrowState)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) : MachineHooks.BorrowState :=
  {tracker with global := {tracker.global with nextPointerTag := successorTag tracker.global.nextPointerTag room}}

def allocatedMachine {K U : Type} (machine : MachineHooks.MachineState K U)
    (tracker : MachineHooks.BorrowState) (room : tracker.global.nextPointerTag.value < 18446744073709551615) :=
  {machine with borrowTracker := some (allocatedTracker tracker room)}

theorem allocate_tag (global : GlobalState) (room : global.nextPointerTag.value < 18446744073709551615) :
    global.newPointerTag = .ok
      ({global with nextPointerTag := successorTag global.nextPointerTag room}, global.nextPointerTag) := by
  have notMax : global.nextPointerTag.value ≠ 18446744073709551615 := by
    intro equal
    rw [equal] at room
    exact (UInt64.lt_irrefl _) room
  simp [GlobalState.newPointerTag,BorTag.succ,BorTag.ofUInt64,notMax,successor_nonzero global.nextPointerTag room,successorTag]

set_option linter.unusedSimpArgs false in
/-- Actual unit retagging, including checked fresh-tag allocation and frame/global
protector registration, from the same initial raw live concrete resources. -/
theorem retag_place_live_concrete {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat)
    (place : MPlaceTy Provenance) (frames : Array F) (frame : F) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (parentTag : BorTag) (parentIndex : UniIndex) (address base : UInt64)
    (encoding : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes address))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : TreeRuntimeInput.TreeFormed entry.allocation.extra tracker.global.nextPointerTag)
    (tagged : entry.allocation.extra.tagMapping.get parentTag = some parentIndex)
    (nodeRoom : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (checkBinding : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (resolveBinding : h.resolveAllocation = TypedValidityProviders.resolveAllocation pointers)
    (truncate : ∀ value, pointers.arithmetic.truncateToTargetUsize value = .ok value)
    (size : h.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (precise : h.preciseInteriorMut = pure false)
    (freeze : h.typeIsFreeze place.layout.ty = pure true)
    (kind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extra : h.ensureTreeExtra = GlobalAllocationMachine.ensure kind globals)
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view =
      {view with machine := {view.machine with memory}}) :
    ∃ finalTree,
      TypedRetag.retagPlace h budget place MachineHooks.protectionPolicy (withCurrent frames frame machine) =
        .ok {place with mplace := {place.mplace with ptr :=
          {place.mplace.ptr with provenance := some (.concrete id tracker.global.nextPointerTag)}}}
          (withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
            {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom)
                tracker.global.nextPointerTag with memory := replaceTree machine.memory id entry finalTree}) ∧
      finalTree.releaseProtector tracker.global.nextPointerTag
          (registeredTracker (allocatedTracker tracker tagRoom) tracker.global.nextPointerTag).global.protectedTags =
        ⟨finalTree,.Released⟩ := by
  obtain ⟨finalTree,reborrow,released⟩ := reborrow_zero_live_concrete h budget place frames frame borrowFrame
    (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) rfl frameBorrow
    id entry parentTag tracker.global.nextPointerTag parentIndex address base encoding cached live tree tagged nodeRoom
    access pointers checkBinding resolveBinding truncate log precise freeze kind globals extra synchronize
  refine ⟨finalTree,?_,released⟩
  unfold TypedRetag.retagPlace
  rw [size]
  simp only [bind,EStateM.bind,pure,EStateM.pure,TypedRetag.tracker_apply,withCurrent,enabled]
  rw [allocate_tag tracker.global tagRoom]
  simp only [TypedRetag.checked_eq,bind,EStateM.bind,pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  erw [reborrow]
  simp only [bind,EStateM.bind,pure,EStateM.pure,encoding,Pointer.new]
  rfl

set_option linter.unusedSimpArgs false in
/-- The complete live-concrete unit argument-protection operation, including
its actual scoped zero-byte uninitialization, from raw initial resources. -/
theorem protect_live_concrete {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat)
    (place : MPlaceTy Provenance) (frames : Array F) (frame : F) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (parentTag : BorTag) (parentIndex : UniIndex) (address base : UInt64)
    (encoding : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes address))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : TreeRuntimeInput.TreeFormed entry.allocation.extra tracker.global.nextPointerTag)
    (tagged : entry.allocation.extra.tagMapping.get parentTag = some parentIndex)
    (nodeRoom : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (checkBinding : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (resolveBinding : h.resolveAllocation = TypedValidityProviders.resolveAllocation pointers)
    (truncate : ∀ value, pointers.arithmetic.truncateToTargetUsize value = .ok value)
    (size : h.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (precise : h.preciseInteriorMut = pure false)
    (freeze : h.typeIsFreeze place.layout.ty = pure true)
    (kind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extra : h.ensureTreeExtra = GlobalAllocationMachine.ensure kind globals)
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view =
      {view with machine := {view.machine with memory}})
    (unitLayout : localMemoryLayout place.layout = ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some place.layout.ty⟩)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (pointerSize : Size)
    (target : access.runtime.pointerSizeIn access.runtime.defaultAddressSpace = .ok pointerSize)
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (writeBinding : ∀ p, h.writeUninit p = (do
      let currentAccess ← ValidityMachine.scopedAccess access
      PlaceMachine.writeMemory currentAccess (fun _ => false) .uninit p)) :
    ∃ finalTree,
      TypedRetag.protectInPlaceFunctionArgument h budget place (withCurrent frames frame machine) =
        .ok () (withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
          {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom)
              tracker.global.nextPointerTag with memory := replaceTree machine.memory id entry finalTree}) ∧
      finalTree.releaseProtector tracker.global.nextPointerTag
          (registeredTracker (allocatedTracker tracker tagRoom) tracker.global.nextPointerTag).global.protectedTags =
        ⟨finalTree,.Released⟩ := by
  obtain ⟨finalTree,retagged,released⟩ := retag_place_live_concrete h budget place frames frame borrowFrame
    machine tracker enabled frameBorrow tagRoom id entry parentTag parentIndex address base encoding cached live tree tagged nodeRoom
    access pointers checkBinding resolveBinding truncate size log precise freeze kind globals extra synchronize
  refine ⟨finalTree,?_,released⟩
  let result : MPlaceTy Provenance := {place with mplace := {place.mplace with ptr :=
    {place.mplace.ptr with provenance := some (.concrete id tracker.global.nextPointerTag)}}}
  let after := withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
    {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom)
      tracker.global.nextPointerTag with memory := replaceTree machine.memory id entry finalTree}
  have resultEncoding : result.mplace = ⟨result.mplace.ptr,.none,none⟩ := by
    simp [result,noMeta,aligned]
  have written := EmptyFunction.UnitProtection.scoped_uninit access result result.mplace.ptr (some place.layout.ty)
    pointerSize unitLayout resultEncoding target retain after
  unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,
    withCurrent,enabled,Option.isSome_some,↓reduceIte]
  erw [retagged]
  simp only [bind,EStateM.bind]
  rw [writeBinding]
  exact written

/-- Actual replacement installs the selected allocation independently of all
other live rows, including their order and contents. -/
theorem replace_lookup {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) :
    (replaceTree memory id entry tree).live.find? (fun row => row.1 == id) =
      some (id,{entry with allocation := entry.allocation.setExtra tree}) := by
  simp [replaceTree,Array.find?_push,Array.find?_filter]
  have emptyFind : memory.live.find? (fun _ => false) = none :=
    Array.find?_eq_none.mpr (by intro row member; simp)
  rw [emptyFind]
  rfl

/-- A second write-back of the same zero-protection tree changes nothing. -/
theorem replace_same {K : Type} (memory : MemoryState Provenance BorrowTree K)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) :
    replaceTree (replaceTree memory id entry tree) id
      {entry with allocation := entry.allocation.setExtra tree} tree = replaceTree memory id entry tree := by
  simp [replaceTree,Array.filter_filter,Allocation.setExtra,Allocation.mapExtra]

private theorem protector_roundtrip (protections : ProtectedTags) (tag : BorTag)
    (fresh : protections.get tag = none) :
    (protections.insert tag .StrongProtector).remove tag = protections := by
  have noFind : protections.entries.find? (fun row => row.1 == tag) = none := by
    cases found : protections.entries.find? (fun row => row.1 == tag) with
    | none => rfl
    | some row => simp [ProtectedTags.get,found] at fresh
  have clean : protections.entries.filter (fun row => row.1 != tag) = protections.entries := by
    apply Array.filter_eq_self.mpr
    intro row member
    have different := Array.find?_eq_none.mp noFind row member
    have ne : row.1 ≠ tag := by simpa only [beq_iff_eq] using different
    simpa only [bne_iff_ne] using ne
  simp [ProtectedTags.insert,ProtectedTags.remove,clean]

set_option linter.unusedSimpArgs false in
/-- Ending the singleton fresh protector follows the actual machine hook:
ensure, tree release, write-back, then global removal. Arbitrary preexisting
global protectors, lower caller frames and unrelated machine data are retained. -/
theorem release_live_singleton {K U : Type} [DecidableEq K]
    (kind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K (PlaceMachine.AccessState K U))
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view =
      {view with machine := {view.machine with memory}})
    (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K) (tree : BorrowTree) (tag : BorTag)
    (fresh : tracker.global.protectedTags.get tag = none)
    (released : tree.releaseProtector tag (registeredTracker tracker tag).global.protectedTags = ⟨tree,.Released⟩) :
    MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure kind globals)
      (withCurrent frames (registeredFrame frame {} id tag)
        {registeredMachine machine tracker tag with memory := replaceTree machine.memory id entry tree}) =
      .ok () (withCurrent frames (registeredFrame frame {} id tag)
        {machine with memory := replaceTree machine.memory id entry tree}) := by
  let updated := {entry with allocation := entry.allocation.setExtra tree}
  let memory := replaceTree machine.memory id entry tree
  let state := withCurrent frames (registeredFrame frame {} id tag)
    {registeredMachine machine tracker tag with memory}
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
  unfold MachineHooks.beforeStackPopWithEnsure
  simp [get,getThe,MonadStateOf.get,EStateM.get,withCurrent,registeredMachine,
    MachineHooks.currentFrame,Stack.currentFrame?,registeredFrame,FrameState.addProtector,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,info]
  erw [ensure]
  simp [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    withCurrent,registeredFrame,registeredMachine,live,Allocation.setExtra,Allocation.mapExtra]
  erw [released]
  simp only [Allocation.setExtra,Allocation.mapExtra] at mutation
  erw [mutation]
  simp only [modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    set,MonadStateOf.set,EStateM.set,GlobalState.endCall,FrameState.addProtector,Array.foldl_push,Array.foldl_empty]
  simp only [registeredTracker,←Array.foldl_toList,List.foldl_cons,List.foldl_nil]
  rw [protector_roundtrip tracker.global.protectedTags tag fresh]
  simp only [enabled]
  rfl

/-- A live concrete unit return destination is protected and later released
through both actual machine operations from initial raw runtime facts. -/
theorem protect_then_release_live_concrete {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat)
    (place : MPlaceTy Provenance) (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (parentTag : BorTag) (parentIndex : UniIndex) (address base : UInt64)
    (encoding : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes address))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : TreeRuntimeInput.TreeFormed entry.allocation.extra tracker.global.nextPointerTag)
    (tagged : entry.allocation.extra.tagMapping.get parentTag = some parentIndex)
    (nodeRoom : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (checkBinding : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (resolveBinding : h.resolveAllocation = TypedValidityProviders.resolveAllocation pointers)
    (truncate : ∀ value, pointers.arithmetic.truncateToTargetUsize value = .ok value)
    (size : h.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (precise : h.preciseInteriorMut = pure false)
    (freeze : h.typeIsFreeze place.layout.ty = pure true)
    (kind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extra : h.ensureTreeExtra = GlobalAllocationMachine.ensure kind globals)
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view =
      {view with machine := {view.machine with memory}})
    (unitLayout : localMemoryLayout place.layout = ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some place.layout.ty⟩)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (pointerSize : Size)
    (target : access.runtime.pointerSizeIn access.runtime.defaultAddressSpace = .ok pointerSize)
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (writeBinding : ∀ p, h.writeUninit p = (do
      let currentAccess ← ValidityMachine.scopedAccess access
      PlaceMachine.writeMemory currentAccess (fun _ => false) .uninit p))
    (globalFormed : TreeRuntimeInput.GlobalFormed tracker.global) :
    ∃ finalTree,
      TypedRetag.protectInPlaceFunctionArgument h budget place (withCurrent frames frame machine) =
        .ok () (withCurrent frames (registeredFrame frame {} id tracker.global.nextPointerTag)
          {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom)
              tracker.global.nextPointerTag with memory := replaceTree machine.memory id entry finalTree}) ∧
      MachineHooks.beforeStackPopWithEnsure (GlobalAllocationMachine.ensure kind globals)
        (withCurrent frames (registeredFrame frame {} id tracker.global.nextPointerTag)
          {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom)
              tracker.global.nextPointerTag with memory := replaceTree machine.memory id entry finalTree}) =
        .ok () (withCurrent frames (registeredFrame frame {} id tracker.global.nextPointerTag)
          {allocatedMachine machine tracker tagRoom with memory := replaceTree machine.memory id entry finalTree}) := by
  obtain ⟨finalTree,protectionEq,released⟩ := protect_live_concrete h budget place frames frame {}
    machine tracker enabled frameBorrow tagRoom id entry parentTag parentIndex address base encoding cached live tree tagged nodeRoom
    access pointers checkBinding resolveBinding truncate size log precise freeze kind globals extra synchronize
    unitLayout noMeta aligned pointerSize target retain writeBinding
  have fresh : (allocatedTracker tracker tagRoom).global.protectedTags.get tracker.global.nextPointerTag = none :=
    globalFormed.nextNotProtected
  have ended := release_live_singleton kind globals synchronize frames frame
    (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) rfl id entry finalTree
    tracker.global.nextPointerTag fresh released
  exact ⟨finalTree,protectionEq,ended⟩

set_option linter.unusedSimpArgs false in
/-- The address-only zero-size branch performs no allocation/tree operation. -/
theorem reborrow_zero_integer {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) (place : MPlaceTy Provenance)
    (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (checkBinding : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (resolveBinding : h.resolveAllocation = TypedValidityProviders.resolveAllocation pointers)
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (encoding : place.mplace.ptr.provenance = none) (tag : BorTag)
    (state : ValidityMachine.State K U) :
    TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag state = .ok none state := by
  have checked : h.checkPtrAccess place.mplace.ptr Size.ZERO state = .ok () state := by
    rw [checkBinding]
    exact EmptyFunction.UnitProtection.check_pointer_zero access place.mplace.ptr state
  have resolved : h.resolveAllocation place.mplace.ptr state = .ok none state := by
    rw [resolveBinding]
    exact EmptyFunction.UnitProtection.resolve_integer pointers place.mplace.ptr encoding state
  unfold TypedRetag.reborrow
  simp only [bind,Bind.bind,EStateM.bind]
  erw [checked]
  simp only [bind,Bind.bind,EStateM.bind]
  erw [resolved]
  simp [log,Size.ZERO,Size.ofBytes,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,encoding]

set_option linter.unusedSimpArgs false in
/-- Checked retagging of an address-only unit place only advances the tag
counter; arbitrary stack, memory, caches and old protectors are unchanged. -/
theorem retag_place_integer {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) (place : MPlaceTy Provenance)
    (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (checkBinding : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (resolveBinding : h.resolveAllocation = TypedValidityProviders.resolveAllocation pointers)
    (size : h.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (encoding : place.mplace.ptr.provenance = none)
    (state : ValidityMachine.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : state.machine.borrowTracker = some tracker)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615) :
    TypedRetag.retagPlace h budget place MachineHooks.protectionPolicy state =
      .ok place {state with machine := allocatedMachine state.machine tracker room} := by
  let after := {state with machine := allocatedMachine state.machine tracker room}
  have borrowed := reborrow_zero_integer h budget place access pointers checkBinding resolveBinding log encoding
    tracker.global.nextPointerTag after
  unfold TypedRetag.retagPlace
  rw [size]
  simp only [TypedRetag.tracker_apply,enabled,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure]
  rw [allocate_tag tracker.global room]
  simp only [TypedRetag.checked_eq,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
  erw [borrowed]
  simp only [bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,encoding]
  have placeSame : {place with mplace := {place.mplace with ptr := {place.mplace.ptr with provenance := none}}} = place := by
    rw [←encoding]
  rw [placeSame]

set_option linter.unusedSimpArgs false in
/-- Address-only unit destinations are protected without imposing backing,
nonnullness, a concrete tag, a cache hit or an empty memory world. -/
theorem protect_integer {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) (place : MPlaceTy Provenance)
    (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (checkBinding : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (resolveBinding : h.resolveAllocation = TypedValidityProviders.resolveAllocation pointers)
    (size : h.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (encoding : place.mplace.ptr.provenance = none)
    (state : ValidityMachine.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : state.machine.borrowTracker = some tracker)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (unitLayout : localMemoryLayout place.layout = ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some place.layout.ty⟩)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (pointerSize : Size)
    (target : access.runtime.pointerSizeIn access.runtime.defaultAddressSpace = .ok pointerSize)
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (writeBinding : ∀ p, h.writeUninit p = (do
      let currentAccess ← ValidityMachine.scopedAccess access
      PlaceMachine.writeMemory currentAccess (fun _ => false) .uninit p)) :
    TypedRetag.protectInPlaceFunctionArgument h budget place state =
      .ok () {state with machine := allocatedMachine state.machine tracker room} := by
  let after := {state with machine := allocatedMachine state.machine tracker room}
  have retagged := retag_place_integer h budget place access pointers checkBinding resolveBinding
    size log encoding state tracker enabled room
  have placeEncoding : place.mplace = ⟨place.mplace.ptr,.none,none⟩ := by
    cases place with
    | mk mplace layout =>
      cases mplace
      simp_all
  have written := EmptyFunction.UnitProtection.scoped_uninit access place place.mplace.ptr (some place.layout.ty)
    pointerSize unitLayout placeEncoding target retain after
  unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,
    enabled,Option.isSome_some,↓reduceIte]
  erw [retagged]
  simp only [bind,Bind.bind,EStateM.bind]
  rw [writeBinding]
  exact written

set_option linter.unusedSimpArgs false in
/-- Internal source composition for a zero reborrow whose current allocation
classification is non-data. No materialization or tree operation is reached. -/
private theorem reborrow_zero_nondata_equations {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K U) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array F) (frame : F) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (id : AllocId) (offset : UInt64) (parent : ProvenanceExtra) (tag : BorTag)
    (check : h.checkPtrAccess place.mplace.ptr Size.ZERO (withCurrent frames frame machine) =
      .ok () (withCurrent frames frame machine))
    (resolve : h.resolveAllocation place.mplace.ptr (withCurrent frames frame machine) =
      .ok (some ⟨id,Size.ofBytes offset,parent⟩) (withCurrent frames frame machine))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (info : AllocationInfo) (classification : machine.memory.getAllocInfo id = .ok info)
    (nondata : info.kind ≠ .liveData) :
    TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy tag
      (withCurrent frames frame machine) =
      .ok (some (.concrete id tag))
        (withCurrent frames (registeredFrame frame borrowFrame id tag) (registeredMachine machine tracker tag)) := by
  let start := withCurrent frames frame machine
  have current : MachineHooks.currentFrame start = .ok frame start := by
    simp [MachineHooks.currentFrame,Stack.currentFrame?,start,withCurrent,
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
  simp [TypedRetag.checked_eq,classification,nondata,Size.ZERO,Size.ofBytes,
    bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,registeredMachine,registeredTracker,registeredFrame]
  rfl

set_option linter.unusedSimpArgs false in
/-- Non-data zero protectors are ended by the actual pop hook without invoking
ensure or any tree operation. No backing allocation or root tag is required. -/
theorem release_nondata_singleton {K U : Type} [DecidableEq K]
    (ensure : AllocId → MachineHooks.M K U Unit) (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K U) (tracker : MachineHooks.BorrowState)
    (enabled : machine.borrowTracker = some tracker) (id : AllocId) (tag : BorTag)
    (fresh : tracker.global.protectedTags.get tag = none)
    (info : AllocationInfo) (classification : machine.memory.getAllocInfo id = .ok info)
    (nondata : info.kind ≠ .liveData) :
    MachineHooks.beforeStackPopWithEnsure ensure
      (withCurrent frames (registeredFrame frame {} id tag) (registeredMachine machine tracker tag)) =
      .ok () (withCurrent frames (registeredFrame frame {} id tag) machine) := by
  simp [MachineHooks.beforeStackPopWithEnsure,withCurrent,registeredFrame,registeredMachine,
    MachineHooks.currentFrame,Stack.currentFrame?,FrameState.addProtector,classification,nondata,
    get,getThe,MonadStateOf.get,EStateM.get,bind,Bind.bind,EStateM.bind,pure,Pure.pure,EStateM.pure,
    set,MonadStateOf.set,EStateM.set,GlobalState.endCall,registeredTracker,←Array.foldl_toList,
    protector_roundtrip tracker.global.protectedTags tag fresh]
  rw [←enabled]

set_option linter.unusedSimpArgs false in
/-- Concrete non-data destinations take both actual protection/pop early-return
branches. All memory is preserved; only the fresh tag counter advances. -/
theorem protect_then_release_nondata_concrete {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) (place : MPlaceTy Provenance)
    (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (globalFormed : TreeRuntimeInput.GlobalFormed tracker.global)
    (id : AllocId) (parentTag : BorTag) (address base : UInt64)
    (encoding : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes address))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (info : AllocationInfo) (classification : machine.memory.getAllocInfo id = .ok info)
    (nondata : info.kind ≠ .liveData)
    (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (checkBinding : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (resolveBinding : h.resolveAllocation = TypedValidityProviders.resolveAllocation pointers)
    (truncate : ∀ value, pointers.arithmetic.truncateToTargetUsize value = .ok value)
    (size : h.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (unitLayout : localMemoryLayout place.layout = ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some place.layout.ty⟩)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (pointerSize : Size)
    (target : access.runtime.pointerSizeIn access.runtime.defaultAddressSpace = .ok pointerSize)
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (writeBinding : ∀ p, h.writeUninit p = (do
      let currentAccess ← ValidityMachine.scopedAccess access
      PlaceMachine.writeMemory currentAccess (fun _ => false) .uninit p)) :
    let after := withCurrent frames (registeredFrame frame {} id tracker.global.nextPointerTag)
      (registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom)
        tracker.global.nextPointerTag)
    TypedRetag.protectInPlaceFunctionArgument h budget place (withCurrent frames frame machine) = .ok () after ∧
      MachineHooks.beforeStackPopWithEnsure h.ensureTreeExtra after =
        .ok () (withCurrent frames (registeredFrame frame {} id tracker.global.nextPointerTag)
          (allocatedMachine machine tracker tagRoom)) := by
  let allocated := withCurrent frames frame (allocatedMachine machine tracker tagRoom)
  let after := withCurrent frames (registeredFrame frame {} id tracker.global.nextPointerTag)
    (registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom)
      tracker.global.nextPointerTag)
  let result : MPlaceTy Provenance := {place with mplace := {place.mplace with ptr :=
    {place.mplace.ptr with provenance := some (.concrete id tracker.global.nextPointerTag)}}}
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO allocated = .ok () allocated := by
    rw [checkBinding]
    exact EmptyFunction.UnitProtection.check_pointer_zero access place.mplace.ptr allocated
  have resolve : h.resolveAllocation place.mplace.ptr allocated =
      .ok (some ⟨id,Size.ofBytes (address-base),.concrete parentTag⟩) allocated := by
    rw [resolveBinding,encoding]
    exact EmptyFunction.UnitProtection.resolve_concrete pointers id parentTag address base truncate allocated cached
  have borrowed := reborrow_zero_nondata_equations h budget place frames frame {}
    (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) rfl frameBorrow
    id (address-base) (.concrete parentTag) tracker.global.nextPointerTag check resolve log info classification nondata
  have retagged : TypedRetag.retagPlace h budget place MachineHooks.protectionPolicy
      (withCurrent frames frame machine) = .ok result after := by
    unfold TypedRetag.retagPlace
    rw [size]
    simp only [bind,EStateM.bind,pure,EStateM.pure,TypedRetag.tracker_apply,withCurrent,enabled]
    rw [allocate_tag tracker.global tagRoom]
    simp only [TypedRetag.checked_eq,bind,EStateM.bind,pure,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
    erw [borrowed]
    simp only [bind,EStateM.bind,pure,EStateM.pure,encoding,Pointer.new,result,after]
  have resultEncoding : result.mplace = ⟨result.mplace.ptr,.none,none⟩ := by simp [result,noMeta,aligned]
  have written := EmptyFunction.UnitProtection.scoped_uninit access result result.mplace.ptr (some place.layout.ty)
    pointerSize unitLayout resultEncoding target retain after
  constructor
  · unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
    simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,withCurrent,
      enabled,Option.isSome_some,↓reduceIte]
    erw [retagged]
    simp only [bind,EStateM.bind]
    rw [writeBinding]
    exact written
  · exact release_nondata_singleton h.ensureTreeExtra frames frame
      (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom) rfl id tracker.global.nextPointerTag
      globalFormed.nextNotProtected info classification nondata

theorem protect_live_concrete_observed {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat)
    (place : MPlaceTy Provenance) (frames : Array F) (frame : F) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (parentTag : BorTag) (parentIndex : UniIndex) (address base : UInt64)
    (encoding : place.mplace.ptr = Pointer.new (some (.concrete id parentTag)) (Size.ofBytes address))
    (cached : machine.user.addresses.baseAddr.find? (fun row => row.allocId == id) = some ⟨id,base⟩)
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : TreeRuntimeInput.TreeFormed entry.allocation.extra tracker.global.nextPointerTag)
    (tagged : entry.allocation.extra.tagMapping.get parentTag = some parentIndex)
    (nodeRoom : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (access : ValidityMachine.Access K U)
    (pointers : PointerMachine.Hooks K (ValidityMachine.Control U))
    (checkBinding : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (resolveBinding : h.resolveAllocation = TypedValidityProviders.resolveAllocation pointers)
    (truncate : ∀ value, pointers.arithmetic.truncateToTargetUsize value = .ok value)
    (size : h.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (precise : h.preciseInteriorMut = pure false)
    (freeze : h.typeIsFreeze place.layout.ty = pure true)
    (kind : K) (globals : GlobalAllocationHooks Provenance BorrowTree K
      (PlaceMachine.AccessState K (ValidityMachine.UserState U)))
    (extra : h.ensureTreeExtra = GlobalAllocationMachine.ensure kind globals)
    (synchronize : ∀ memory view, globals.synchronizeMemory memory view =
      {view with machine := {view.machine with memory}})
    (unitLayout : localMemoryLayout place.layout = ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some place.layout.ty⟩)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (pointerSize : Size)
    (target : access.runtime.pointerSizeIn access.runtime.defaultAddressSpace = .ok pointerSize)
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (writeBinding : ∀ p, h.writeUninit p = (do
      let currentAccess ← ValidityMachine.scopedAccess access
      PlaceMachine.writeMemory currentAccess (fun _ => false) .uninit p)) :
    ∃ finalTree,
      TypedRetag.protectInPlaceFunctionArgument h budget place (withCurrent frames frame machine) =
        .ok () (withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
          {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom)
              tracker.global.nextPointerTag with memory := replaceTree machine.memory id entry finalTree}) ∧
      finalTree.releaseProtector tracker.global.nextPointerTag
          (registeredTracker (allocatedTracker tracker tagRoom) tracker.global.nextPointerTag).global.protectedTags =
        ⟨finalTree,.Released⟩ ∧
      entry.allocation.extra.newChild (Size.ofBytes (address-base)) (.concrete parentTag)
        tracker.global.nextPointerTag (DedupRangeMap.new Size.ZERO (⟨.ReservedFrz false,false,.None⟩ : LocationState))
        (.ReservedFrz false) true = ⟨finalTree,.ok ()⟩ := by
  let entered := allocatedMachine machine tracker tagRoom
  let enteredTracker := allocatedTracker tracker tagRoom
  let start := withCurrent frames frame entered
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO start = .ok () start := by
    rw [checkBinding]
    exact EmptyFunction.UnitProtection.check_pointer_zero access place.mplace.ptr start
  have resolve : h.resolveAllocation place.mplace.ptr start =
      .ok (some ⟨id,Size.ofBytes (address-base),.concrete parentTag⟩) start := by
    rw [resolveBinding,encoding]
    exact EmptyFunction.UnitProtection.resolve_concrete pointers id parentTag address base truncate start cached
  obtain ⟨finalTree,child,released⟩ := tree.constructAndRelease parentTag parentIndex tagged nodeRoom
    (Size.ofBytes (address-base)) ⟨.ReservedFrz false,false,.None⟩
    (registeredTracker enteredTracker tracker.global.nextPointerTag).global.protectedTags
  have reborrow := reborrow_zero_live_equations h budget place frames frame borrowFrame entered enteredTracker rfl
    frameBorrow id entry (address-base) (.concrete parentTag) tracker.global.nextPointerTag check resolve
    log precise freeze kind globals extra synchronize live finalTree child
  let result : MPlaceTy Provenance := {place with mplace := {place.mplace with ptr :=
    {place.mplace.ptr with provenance := some (.concrete id tracker.global.nextPointerTag)}}}
  let after := withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
    {registeredMachine entered enteredTracker tracker.global.nextPointerTag with
      memory := replaceTree machine.memory id entry finalTree}
  have retagged : TypedRetag.retagPlace h budget place MachineHooks.protectionPolicy
      (withCurrent frames frame machine) = .ok result after := by
    unfold TypedRetag.retagPlace
    rw [size]
    simp only [bind,EStateM.bind,pure,EStateM.pure,TypedRetag.tracker_apply,withCurrent,enabled]
    rw [allocate_tag tracker.global tagRoom]
    simp only [TypedRetag.checked_eq,bind,EStateM.bind,pure,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
    erw [reborrow]
    simp only [bind,EStateM.bind,pure,EStateM.pure,encoding,Pointer.new]
    simp only [result,after,entered,enteredTracker,allocatedMachine,encoding,Pointer.new]
  refine ⟨finalTree,?_,released,child⟩
  have resultEncoding : result.mplace = ⟨result.mplace.ptr,.none,none⟩ := by
    simp [result,noMeta,aligned]
  have written := EmptyFunction.UnitProtection.scoped_uninit access result result.mplace.ptr (some place.layout.ty)
    pointerSize unitLayout resultEncoding target retain after
  unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,withCurrent,enabled,
    Option.isSome_some,↓reduceIte]
  erw [retagged]
  simp only [bind,EStateM.bind]
  rw [writeBinding]
  exact written

/-- Internal operation-composition edge, shared by concrete and wildcard
parents. Caller admission must derive its source equations independently. -/
abbrev reborrow_zero_live_from_equations := @reborrow_zero_live_equations
abbrev reborrow_zero_nondata_from_equations := @reborrow_zero_nondata_equations

end EmptyFunction.UnitRetag
