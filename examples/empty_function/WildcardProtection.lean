import empty_function.WildcardCanonical
import empty_function.FrameExit
import empty_function.ProtectionPlace

/-! Source protection adapters after the derived wildcard zero-size resolution.
Implementation equations are private composition edges; public admission uses
raw current input and invokes the resolver itself. No wildcard body is added. -/
namespace EmptyFunction.WildcardProtection
open Miri Miri.ABI Miri.Memory Miri.MIR Miri.TreeBorrows Miri.DataStructures Miri.Interpreter
open Miri.TreeBorrows.Tree
open EmptyFunction.Configuration EmptyFunction.CanonicalDictionaries EmptyFunction.WholeCall EmptyFunction.Specification EmptyFunction.UnitRetag
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
private theorem protect_live_from_resolution {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat)
    (place : MPlaceTy Provenance) (frames : Array F) (frame : F) (borrowFrame : FrameState)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some borrowFrame)
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (entry : LocalAllocation Provenance BorrowTree K)
    (offset : UInt64) (wild : place.mplace.ptr.provenance = some .wildcard)
    (resolved : h.resolveAllocation place.mplace.ptr
      (withCurrent frames frame (allocatedMachine machine tracker tagRoom)) =
      .ok (some ⟨id,Size.ofBytes offset,.wildcard⟩)
        (withCurrent frames frame (allocatedMachine machine tracker tagRoom)))
    (live : machine.memory.live.find? (fun row => row.1 == id) = some (id,entry))
    (tree : TreeRuntimeInput.TreeFormed entry.allocation.extra tracker.global.nextPointerTag)
    (nodeRoom : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295)
    (access : ValidityMachine.Access K U)
    (checkBinding : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
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
      PlaceMachine.writeUninitMemory currentAccess p)) :
    ∃ finalTree,
      TypedRetag.protectInPlaceFunctionArgument h budget place (withCurrent frames frame machine) =
        .ok () (withCurrent frames (registeredFrame frame borrowFrame id tracker.global.nextPointerTag)
          {registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom)
              tracker.global.nextPointerTag with memory := replaceTree machine.memory id entry finalTree}) ∧
      finalTree.releaseProtector tracker.global.nextPointerTag
          (registeredTracker (allocatedTracker tracker tagRoom) tracker.global.nextPointerTag).global.protectedTags =
        ⟨finalTree,.Released⟩ ∧
      entry.allocation.extra.newChild (Size.ofBytes offset) .wildcard
        tracker.global.nextPointerTag (DedupRangeMap.new Size.ZERO (⟨.ReservedFrz false,false,.None⟩ : LocationState))
        (.ReservedFrz false) true = ⟨finalTree,.ok ()⟩ := by
  let entered := allocatedMachine machine tracker tagRoom
  let enteredTracker := allocatedTracker tracker tagRoom
  let start := withCurrent frames frame entered
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO start = .ok () start := by
    rw [checkBinding]
    exact EmptyFunction.UnitProtection.check_pointer_zero access place.mplace.ptr start
  have resolve : h.resolveAllocation place.mplace.ptr start =
      .ok (some ⟨id,Size.ofBytes offset,.wildcard⟩) start := resolved
  obtain ⟨finalTree,child,released⟩ := tree.wildcardConstructAndRelease nodeRoom
    (Size.ofBytes offset) ⟨.ReservedFrz false,false,.None⟩
    (registeredTracker enteredTracker tracker.global.nextPointerTag).global.protectedTags
  have reborrow := reborrow_zero_live_from_equations h budget place frames frame borrowFrame entered enteredTracker rfl
    frameBorrow id entry offset .wildcard tracker.global.nextPointerTag check resolve
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
    simp only [bind,EStateM.bind,pure,EStateM.pure,Pointer.new,wild]
    simp only [result,after,entered,enteredTracker,allocatedMachine,Pointer.new,wild]
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


private theorem protect_nondata_from_resolution {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat)
    (place : MPlaceTy Provenance) (frames : Array F) (frame : F)
    (machine : MachineHooks.MachineState K (ValidityMachine.UserState U))
    (tracker : MachineHooks.BorrowState) (enabled : machine.borrowTracker = some tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (tagRoom : tracker.global.nextPointerTag.value < 18446744073709551615)
    (id : AllocId) (info : AllocationInfo)
    (classification : machine.memory.getAllocInfo id = .ok info) (nondata : info.kind ≠ .liveData)
    (offset : UInt64) (wild : place.mplace.ptr.provenance = some .wildcard)
    (resolved : h.resolveAllocation place.mplace.ptr
      (withCurrent frames frame (allocatedMachine machine tracker tagRoom)) =
      .ok (some ⟨id,Size.ofBytes offset,.wildcard⟩)
        (withCurrent frames frame (allocatedMachine machine tracker tagRoom)))
    (access : ValidityMachine.Access K U)
    (checkBinding : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (size : h.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (unitLayout : localMemoryLayout place.layout = ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some place.layout.ty⟩)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (pointerSize : Size)
    (target : access.runtime.pointerSizeIn access.runtime.defaultAddressSpace = .ok pointerSize)
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (writeBinding : ∀ p, h.writeUninit p = (do
      let currentAccess ← ValidityMachine.scopedAccess access
      PlaceMachine.writeUninitMemory currentAccess p)) :
    TypedRetag.protectInPlaceFunctionArgument h budget place (withCurrent frames frame machine) =
      .ok () (withCurrent frames (registeredFrame frame {} id tracker.global.nextPointerTag)
        (registeredMachine (allocatedMachine machine tracker tagRoom) (allocatedTracker tracker tagRoom)
          tracker.global.nextPointerTag)) := by
  let entered := allocatedMachine machine tracker tagRoom
  let enteredTracker := allocatedTracker tracker tagRoom
  let start := withCurrent frames frame entered
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO start = .ok () start := by
    rw [checkBinding]
    exact EmptyFunction.UnitProtection.check_pointer_zero access place.mplace.ptr start
  have resolve : h.resolveAllocation place.mplace.ptr start =
      .ok (some ⟨id,Size.ofBytes offset,.wildcard⟩) start := resolved
  have reborrow := reborrow_zero_nondata_from_equations h budget place frames frame {}
    entered enteredTracker rfl frameBorrow id offset .wildcard tracker.global.nextPointerTag check resolve
    log info classification nondata
  let result : MPlaceTy Provenance := {place with mplace := {place.mplace with ptr :=
    {place.mplace.ptr with provenance := some (.concrete id tracker.global.nextPointerTag)}}}
  let after := withCurrent frames (registeredFrame frame {} id tracker.global.nextPointerTag)
    (registeredMachine entered enteredTracker tracker.global.nextPointerTag)
  have retagged : TypedRetag.retagPlace h budget place MachineHooks.protectionPolicy
      (withCurrent frames frame machine) = .ok result after := by
    unfold TypedRetag.retagPlace
    rw [size]
    simp only [bind,EStateM.bind,pure,EStateM.pure,TypedRetag.tracker_apply,withCurrent,enabled]
    rw [allocate_tag tracker.global tagRoom]
    simp only [TypedRetag.checked_eq,bind,EStateM.bind,pure,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
    erw [reborrow]
    simp only [bind,EStateM.bind,pure,EStateM.pure,Pointer.new,wild]
    simp only [result,after,entered,enteredTracker,allocatedMachine,Pointer.new,wild]
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


/-- Internal unresolved branch of the actual protection operation. -/
private theorem protect_miss_from_resolution {K U : Type} [DecidableEq K]
    (h : TypedRetag.Hooks K (ValidityMachine.UserState U)) (budget : Nat) (place : MPlaceTy Provenance)
    (access : ValidityMachine.Access K U)
    (checkBinding : h.checkPtrAccess = ValidityMachine.checkPointerAccess access)
    (size : h.sizeAndAlign place = pure (some (Size.ZERO,Align.ONE)))
    (log : h.logCreation = fun _ _ _ _ _ => pure ())
    (wild : place.mplace.ptr.provenance = some .wildcard)
    (state : ValidityMachine.State K U) (tracker : MachineHooks.BorrowState)
    (enabled : state.machine.borrowTracker = some tracker)
    (room : tracker.global.nextPointerTag.value < 18446744073709551615)
    (resolved : h.resolveAllocation place.mplace.ptr
      {state with machine := allocatedMachine state.machine tracker room} =
      .ok none {state with machine := allocatedMachine state.machine tracker room})
    (unitLayout : localMemoryLayout place.layout = ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some place.layout.ty⟩)
    (noMeta : place.mplace.metadata = .none) (aligned : place.mplace.misaligned = none)
    (pointerSize : Size)
    (target : access.runtime.pointerSizeIn access.runtime.defaultAddressSpace = .ok pointerSize)
    (retain : ∀ machine, access.retainTouched machine none = machine)
    (writeBinding : ∀ p, h.writeUninit p = (do
      let currentAccess ← ValidityMachine.scopedAccess access
      PlaceMachine.writeUninitMemory currentAccess p)) :
    TypedRetag.protectInPlaceFunctionArgument h budget place state =
      .ok () {state with machine := allocatedMachine state.machine tracker room} := by
  let after := {state with machine := allocatedMachine state.machine tracker room}
  let result : MPlaceTy Provenance := place
  have check : h.checkPtrAccess place.mplace.ptr Size.ZERO after = .ok () after := by
    rw [checkBinding];exact UnitProtection.check_pointer_zero access _ _
  have resolve : h.resolveAllocation place.mplace.ptr after = .ok none after := resolved
  have borrowed : TypedRetag.reborrow h budget place Size.ZERO MachineHooks.protectionPolicy
      tracker.global.nextPointerTag after = .ok place.mplace.ptr.provenance after := by
    unfold TypedRetag.reborrow
    simp only [check,resolve,log,bind,EStateM.bind,pure,EStateM.pure]
    with_unfolding_all rfl
  have retagged : TypedRetag.retagPlace h budget place MachineHooks.protectionPolicy state =
      .ok result after := by
    unfold TypedRetag.retagPlace
    rw [size]
    simp only [TypedRetag.tracker_apply,enabled,bind,EStateM.bind,pure,EStateM.pure]
    rw [allocate_tag tracker.global room]
    simp only [TypedRetag.checked_eq,bind,EStateM.bind,pure,EStateM.pure,
      modify,modifyGet,MonadStateOf.modifyGet,EStateM.modifyGet]
    erw [borrowed]
    simp only [wild,result,after,bind,EStateM.bind,pure,EStateM.pure]
    rw [←wild]
  have resultEncoding : result.mplace = ⟨result.mplace.ptr,.none,none⟩ := by
    change place.mplace = ⟨place.mplace.ptr,.none,none⟩
    rw [←noMeta,←aligned]
  have written := UnitProtection.scoped_uninit access result result.mplace.ptr (some place.layout.ty)
    pointerSize unitLayout resultEncoding target retain after
  unfold TypedRetag.protectInPlaceFunctionArgument TypedRetag.protectPlace
  simp only [get,getThe,MonadStateOf.get,EStateM.get,bind,EStateM.bind,enabled,Option.isSome_some,↓reduceIte]
  erw [retagged]
  simp only [bind,EStateM.bind]
  rw [writeBinding]
  exact written

/-- Raw wildcard admission is resolved once, then every live hit is protected
through the shared real reborrow/write pipeline. The result includes the actual
constructor equation for subsequent rights and release composition. Misses and
non-live hits remain available for the existing no-node/materialization families. -/
theorem dispatch (s : Static) (metadata : Metadata s) (profile : Profile s) (capacity : 0 < s.capacity)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p) (resources : ResourceMargins s p)
    (destination : InputDraft.MemoryDestination s p input.tracker)
    (wild : destination.place.mplace.ptr.provenance = some .wildcard)
    (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (enabled : machine.borrowTracker = some input.tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (memory : machine.memory = p.before.machine.memory)
    (addresses : machine.user.addresses = p.before.machine.user.addresses) :
    ∃ answer,
      s.cfg.retag.resolveAllocation destination.place.mplace.ptr
        (LocalUnit.current p.before.stack.frames frame
          (allocatedMachine machine input.tracker (ConcreteProtection.tag_room s p input resources))) =
        .ok answer (LocalUnit.current p.before.stack.frames frame
          (allocatedMachine machine input.tracker (ConcreteProtection.tag_room s p input resources))) ∧
      WildcardResolution.Hits s p.before destination.place.mplace.ptr answer ∧
      (answer = none →
        let after := LocalUnit.current p.before.stack.frames frame
          (allocatedMachine machine input.tracker (ConcreteProtection.tag_room s p input resources))
        TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
          (LocalUnit.current p.before.stack.frames frame machine) = .ok () after ∧
        MachineHooks.beforeStackPopWithEnsure s.cfg.retag.ensureTreeExtra after = .ok () after) ∧
      (∀ (id : AllocId) (offset : Size) (info : AllocationInfo),
        answer = some ⟨id,offset,.wildcard⟩ →
        p.before.machine.memory.getAllocInfo id = .ok info → info.kind ≠ .liveData →
        let entered := allocatedMachine machine input.tracker (ConcreteProtection.tag_room s p input resources)
        let enteredTracker := allocatedTracker input.tracker (ConcreteProtection.tag_room s p input resources)
        let registered := LocalUnit.current p.before.stack.frames
          (registeredFrame frame {} id input.tracker.global.nextPointerTag)
          (registeredMachine entered enteredTracker input.tracker.global.nextPointerTag)
        TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
          (LocalUnit.current p.before.stack.frames frame machine) = .ok () registered ∧
        MachineHooks.beforeStackPopWithEnsure s.cfg.retag.ensureTreeExtra registered =
          .ok () (LocalUnit.current p.before.stack.frames
            (registeredFrame frame {} id input.tracker.global.nextPointerTag) entered)) ∧
      ∀ (id : AllocId) (offset : Size) (entry : InputDraft.Entry),
        answer = some ⟨id,offset,.wildcard⟩ →
        p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry) →
        ∃ tree,
          TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
            (LocalUnit.current p.before.stack.frames frame machine) =
            .ok () (LocalUnit.current p.before.stack.frames
              (registeredFrame frame {} id input.tracker.global.nextPointerTag)
              (ConcreteProtection.protectedMachine machine input.tracker
                (ConcreteProtection.tag_room s p input resources) id entry tree)) ∧
          tree.releaseProtector input.tracker.global.nextPointerTag
            (registeredTracker (allocatedTracker input.tracker (ConcreteProtection.tag_room s p input resources))
              input.tracker.global.nextPointerTag).global.protectedTags = ⟨tree,.Released⟩ ∧
          entry.allocation.extra.newChild offset .wildcard input.tracker.global.nextPointerTag
            (DedupRangeMap.new Size.ZERO (⟨.ReservedFrz false,false,.None⟩ : LocationState))
            (.ReservedFrz false) true = ⟨tree,.ok ()⟩ ∧
          MachineHooks.beforeStackPopWithEnsure s.cfg.retag.ensureTreeExtra
            (LocalUnit.current p.before.stack.frames
              (registeredFrame frame {} id input.tracker.global.nextPointerTag)
              (ConcreteProtection.protectedMachine machine input.tracker
                (ConcreteProtection.tag_room s p input resources) id entry tree)) =
            .ok () (LocalUnit.current p.before.stack.frames
              (registeredFrame frame {} id input.tracker.global.nextPointerTag)
              (ConcreteProtection.releasedMachine machine input.tracker
                (ConcreteProtection.tag_room s p input resources) id entry tree)) := by
  let room := ConcreteProtection.tag_room s p input resources
  let entered := LocalUnit.current p.before.stack.frames frame (allocatedMachine machine input.tracker room)
  obtain ⟨answer,resolve,typed,hits⟩ := WildcardCanonical.resolve s metadata capacity p.before entered
    memory addresses input.tracker destination.place.mplace.ptr destination.pointer wild
  have dictionaries := MetadataBinding.fields s metadata capacity
  obtain ⟨_,ensure,synchronize⟩ := ConcreteProtection.bindings s metadata capacity
  have size : s.cfg.retag.sizeAndAlign destination.place = pure (some (Size.ZERO,Align.ONE)) := by
    have sized : destination.place.layout.layout.isSized = true := by
      rw [destination.layout]; exact metadata.unitSized
    simpa only [destination.layout,metadata.unitSize,metadata.unitAlign] using
      dictionaries.sizeAndAlign destination.place sized
  have unitLayout : localMemoryLayout destination.place.layout =
      ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some destination.place.layout.ty⟩ := by
    simp [localMemoryLayout,destination.layout,metadata.unitSize,metadata.unitAlign,metadata.unitBackend]
  have target : s.cfg.access.runtime.pointerSizeIn s.cfg.access.runtime.defaultAddressSpace =
      .ok s.cfg.access.runtime.pointerSize := by
    simp [RuntimeTargetDataLayout.pointerSizeIn,RuntimeTargetDataLayout.pointerSpecIn,
      RuntimeTargetDataLayout.pointerSize,Except.pure]
    rfl
  refine ⟨answer,resolve,hits,?_,?_,?_⟩
  · intro unresolved
    refine ⟨?_,?_⟩
    · exact protect_miss_from_resolution s.cfg.retag s.limits.retag destination.place
        s.cfg.access dictionaries.checkPtrAccess size dictionaries.log wild
        (LocalUnit.current p.before.stack.frames frame machine) input.tracker enabled room
        (by rw [unresolved] at resolve;exact resolve) unitLayout destination.sizedMetadata destination.alignmentCache
        s.cfg.access.runtime.pointerSize target (fun machine => by rw [dictionaries.retainTouched]) dictionaries.writeUninit
    · exact FrameExit.release_empty s.cfg.retag.ensureTreeExtra p.before.stack.frames frame
        (allocatedMachine machine input.tracker room) (allocatedTracker input.tracker room) {} rfl frameBorrow rfl
  · intro id offset info result classification nondata
    cases offset with
    | mk relative =>
      have classNow : machine.memory.getAllocInfo id = .ok info := by rw [memory];exact classification
      have protectionEq := protect_nondata_from_resolution s.cfg.retag s.limits.retag destination.place
        p.before.stack.frames frame machine input.tracker enabled frameBorrow room id info classNow nondata
        relative wild (by rw [result] at resolve;exact resolve) s.cfg.access dictionaries.checkPtrAccess
        size dictionaries.log unitLayout destination.sizedMetadata destination.alignmentCache
        s.cfg.access.runtime.pointerSize target (fun machine => by rw [dictionaries.retainTouched]) dictionaries.writeUninit
      have ended := UnitRetag.release_nondata_singleton s.cfg.retag.ensureTreeExtra p.before.stack.frames frame
        (allocatedMachine machine input.tracker room) (allocatedTracker input.tracker room) rfl id
        input.tracker.global.nextPointerTag input.world.globals.nextNotProtected info classNow nondata
      exact ⟨protectionEq,ended⟩
  · intro id offset entry result live
    have member := Array.mem_of_find?_eq_some live
    obtain ⟨formed⟩ := input.world.liveTrees (id,entry) member
    have nodeRoom : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295 := by
      have bound : entry.allocation.extra.nodes.size + resources.budget < 2^32 := resources.nodeRoom (id,entry) member
      have account : entry.allocation.extra.tagMapping.mapping.size + entry.allocation.extra.tagMapping.deassigned.size = entry.allocation.extra.nodes.size := formed.accounting
      omega
    cases offset with
    | mk relative =>
      obtain ⟨tree,protectionEq,released,child⟩ := protect_live_from_resolution s.cfg.retag s.limits.retag destination.place
        p.before.stack.frames frame {} machine input.tracker enabled frameBorrow room id entry relative wild
        (by rw [result] at resolve;exact resolve) (by rw [memory];exact live) formed nodeRoom
        s.cfg.access dictionaries.checkPtrAccess size dictionaries.log
        (by rw [dictionaries.precise,profile.precise])
        (by apply dictionaries.freeze;rw [destination.layout];exact metadata.unitFreeze)
        .global (ConcreteProtection.source s).globals ensure synchronize unitLayout destination.sizedMetadata
        destination.alignmentCache s.cfg.access.runtime.pointerSize target
        (fun machine => by rw [dictionaries.retainTouched]) dictionaries.writeUninit
      have ended := ConcreteProtection.release s metadata capacity p.before.stack.frames frame
        (allocatedMachine machine input.tracker room) input.tracker room rfl input.world.globals id entry tree released
      exact ⟨tree,protectionEq,released,child,ended⟩



theorem dispatch_stage (s : Static) (metadata : Metadata s) (profile : Profile s) (capacity : 0 < s.capacity)
    (p : Packet) (input : InputDraft.CurrentInputDraft s p) (resources : ResourceMargins s p)
    (destination : ProtectionPlace.Input s p.before input.tracker)
    (wild : destination.place.mplace.ptr.provenance = some .wildcard)
    (frames : Array LocalUnit.F) (frame : LocalUnit.F) (machine : MachineHooks.MachineState MiriMemoryKind RootUser)
    (enabled : machine.borrowTracker = some input.tracker)
    (frameBorrow : frame.extra.borrowTracker = some {})
    (memory : machine.memory = p.before.machine.memory)
    (addresses : machine.user.addresses = p.before.machine.user.addresses) :
    ∃ answer,
      s.cfg.retag.resolveAllocation destination.place.mplace.ptr
        (LocalUnit.current frames frame
          (allocatedMachine machine input.tracker (ConcreteProtection.tag_room s p input resources))) =
        .ok answer (LocalUnit.current frames frame
          (allocatedMachine machine input.tracker (ConcreteProtection.tag_room s p input resources))) ∧
      WildcardResolution.Hits s p.before destination.place.mplace.ptr answer ∧
      (answer = none →
        let after := LocalUnit.current frames frame
          (allocatedMachine machine input.tracker (ConcreteProtection.tag_room s p input resources))
        TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
          (LocalUnit.current frames frame machine) = .ok () after ∧
        MachineHooks.beforeStackPopWithEnsure s.cfg.retag.ensureTreeExtra after = .ok () after) ∧
      (∀ (id : AllocId) (offset : Size) (info : AllocationInfo),
        answer = some ⟨id,offset,.wildcard⟩ →
        p.before.machine.memory.getAllocInfo id = .ok info → info.kind ≠ .liveData →
        let entered := allocatedMachine machine input.tracker (ConcreteProtection.tag_room s p input resources)
        let enteredTracker := allocatedTracker input.tracker (ConcreteProtection.tag_room s p input resources)
        let registered := LocalUnit.current frames
          (registeredFrame frame {} id input.tracker.global.nextPointerTag)
          (registeredMachine entered enteredTracker input.tracker.global.nextPointerTag)
        TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
          (LocalUnit.current frames frame machine) = .ok () registered ∧
        MachineHooks.beforeStackPopWithEnsure s.cfg.retag.ensureTreeExtra registered =
          .ok () (LocalUnit.current frames
            (registeredFrame frame {} id input.tracker.global.nextPointerTag) entered)) ∧
      ∀ (id : AllocId) (offset : Size) (entry : InputDraft.Entry),
        answer = some ⟨id,offset,.wildcard⟩ →
        p.before.machine.memory.live.find? (fun row => row.1 == id) = some (id,entry) →
        ∃ tree,
          TypedRetag.protectInPlaceFunctionArgument s.cfg.retag s.limits.retag destination.place
            (LocalUnit.current frames frame machine) =
            .ok () (LocalUnit.current frames
              (registeredFrame frame {} id input.tracker.global.nextPointerTag)
              (ConcreteProtection.protectedMachine machine input.tracker
                (ConcreteProtection.tag_room s p input resources) id entry tree)) ∧
          tree.releaseProtector input.tracker.global.nextPointerTag
            (registeredTracker (allocatedTracker input.tracker (ConcreteProtection.tag_room s p input resources))
              input.tracker.global.nextPointerTag).global.protectedTags = ⟨tree,.Released⟩ ∧
          entry.allocation.extra.newChild offset .wildcard input.tracker.global.nextPointerTag
            (DedupRangeMap.new Size.ZERO (⟨.ReservedFrz false,false,.None⟩ : LocationState))
            (.ReservedFrz false) true = ⟨tree,.ok ()⟩ ∧
          MachineHooks.beforeStackPopWithEnsure s.cfg.retag.ensureTreeExtra
            (LocalUnit.current frames
              (registeredFrame frame {} id input.tracker.global.nextPointerTag)
              (ConcreteProtection.protectedMachine machine input.tracker
                (ConcreteProtection.tag_room s p input resources) id entry tree)) =
            .ok () (LocalUnit.current frames
              (registeredFrame frame {} id input.tracker.global.nextPointerTag)
              (ConcreteProtection.releasedMachine machine input.tracker
                (ConcreteProtection.tag_room s p input resources) id entry tree)) := by
  let room := ConcreteProtection.tag_room s p input resources
  let entered := LocalUnit.current frames frame (allocatedMachine machine input.tracker room)
  obtain ⟨answer,resolve,typed,hits⟩ := WildcardCanonical.resolve s metadata capacity p.before entered
    memory addresses input.tracker destination.place.mplace.ptr destination.pointer wild
  have dictionaries := MetadataBinding.fields s metadata capacity
  obtain ⟨_,ensure,synchronize⟩ := ConcreteProtection.bindings s metadata capacity
  have size : s.cfg.retag.sizeAndAlign destination.place = pure (some (Size.ZERO,Align.ONE)) := by
    have sized : destination.place.layout.layout.isSized = true := by
      rw [destination.layout]; exact metadata.unitSized
    simpa only [destination.layout,metadata.unitSize,metadata.unitAlign] using
      dictionaries.sizeAndAlign destination.place sized
  have unitLayout : localMemoryLayout destination.place.layout =
      ⟨Size.ZERO,Align.ONE,.Memory (sized := true),some destination.place.layout.ty⟩ := by
    simp [localMemoryLayout,destination.layout,metadata.unitSize,metadata.unitAlign,metadata.unitBackend]
  have target : s.cfg.access.runtime.pointerSizeIn s.cfg.access.runtime.defaultAddressSpace =
      .ok s.cfg.access.runtime.pointerSize := by
    simp [RuntimeTargetDataLayout.pointerSizeIn,RuntimeTargetDataLayout.pointerSpecIn,
      RuntimeTargetDataLayout.pointerSize,Except.pure]
    rfl
  refine ⟨answer,resolve,hits,?_,?_,?_⟩
  · intro unresolved
    refine ⟨?_,?_⟩
    · exact protect_miss_from_resolution s.cfg.retag s.limits.retag destination.place
        s.cfg.access dictionaries.checkPtrAccess size dictionaries.log wild
        (LocalUnit.current frames frame machine) input.tracker enabled room
        (by rw [unresolved] at resolve;exact resolve) unitLayout destination.sizedMetadata destination.alignmentCache
        s.cfg.access.runtime.pointerSize target (fun machine => by rw [dictionaries.retainTouched]) dictionaries.writeUninit
    · exact FrameExit.release_empty s.cfg.retag.ensureTreeExtra frames frame
        (allocatedMachine machine input.tracker room) (allocatedTracker input.tracker room) {} rfl frameBorrow rfl
  · intro id offset info result classification nondata
    cases offset with
    | mk relative =>
      have classNow : machine.memory.getAllocInfo id = .ok info := by rw [memory];exact classification
      have protectionEq := protect_nondata_from_resolution s.cfg.retag s.limits.retag destination.place
        frames frame machine input.tracker enabled frameBorrow room id info classNow nondata
        relative wild (by rw [result] at resolve;exact resolve) s.cfg.access dictionaries.checkPtrAccess
        size dictionaries.log unitLayout destination.sizedMetadata destination.alignmentCache
        s.cfg.access.runtime.pointerSize target (fun machine => by rw [dictionaries.retainTouched]) dictionaries.writeUninit
      have ended := UnitRetag.release_nondata_singleton s.cfg.retag.ensureTreeExtra frames frame
        (allocatedMachine machine input.tracker room) (allocatedTracker input.tracker room) rfl id
        input.tracker.global.nextPointerTag input.world.globals.nextNotProtected info classNow nondata
      exact ⟨protectionEq,ended⟩
  · intro id offset entry result live
    have member := Array.mem_of_find?_eq_some live
    obtain ⟨formed⟩ := input.world.liveTrees (id,entry) member
    have nodeRoom : entry.allocation.extra.tagMapping.mapping.size ≤ 4294967295 := by
      have bound : entry.allocation.extra.nodes.size + resources.budget < 2^32 := resources.nodeRoom (id,entry) member
      have account : entry.allocation.extra.tagMapping.mapping.size + entry.allocation.extra.tagMapping.deassigned.size = entry.allocation.extra.nodes.size := formed.accounting
      omega
    cases offset with
    | mk relative =>
      obtain ⟨tree,protectionEq,released,child⟩ := protect_live_from_resolution s.cfg.retag s.limits.retag destination.place
        frames frame {} machine input.tracker enabled frameBorrow room id entry relative wild
        (by rw [result] at resolve;exact resolve) (by rw [memory];exact live) formed nodeRoom
        s.cfg.access dictionaries.checkPtrAccess size dictionaries.log
        (by rw [dictionaries.precise,profile.precise])
        (by apply dictionaries.freeze;rw [destination.layout];exact metadata.unitFreeze)
        .global (ConcreteProtection.source s).globals ensure synchronize unitLayout destination.sizedMetadata
        destination.alignmentCache s.cfg.access.runtime.pointerSize target
        (fun machine => by rw [dictionaries.retainTouched]) dictionaries.writeUninit
      have ended := ConcreteProtection.release s metadata capacity frames frame
        (allocatedMachine machine input.tracker room) input.tracker room rfl input.world.globals id entry tree released
      exact ⟨tree,protectionEq,released,child,ended⟩




end EmptyFunction.WildcardProtection
